import GaloisForLFunctions.RHTower.SelbergPoincarePole
import GaloisForLFunctions.RHTower.SelbergModalEnergy
import GaloisForLFunctions.RHTower.SarnakXueCuspMode

open Complex MeasureTheory Topology Metric UpperHalfPlane Set Filter
open scoped MatrixGroups

/-!
# Selberg's `λ₁ ≥ 3/16` for every principal congruence subgroup

Let `f` be a `Γ(N)` Maass cusp form (`N ≥ 3`) with `λ = s₀(1 - s₀)`, `3/4 < s₀ < 1`, i.e. `0 < λ < 3/16`. For
`m ≥ 1` pair the Poincaré series with `g = f` (and with `g = f̄` for the positive modes). By unfolding, for
`Re s > 1` the pairing is `N ∫_0^∞ y^{s-2} e^{-2πmy/N} a_{-m}(y) dy`; by the Fourier–Kloosterman expansion and
Weil's bound it continues holomorphically to `Re s > 3/4`. The identity theorem makes the Mellin side bounded as
`s ↓ s₀`, so the leading coefficient `α` of `a_{-m}(y) = α y^{1-s₀} + O(y^{s₀})` vanishes (`alpha_zero_of_pairing`),
and then the energy argument forces `a_{-m} ≡ 0`. All modes vanish, so `f = 0` by pointwise Fourier inversion
(`selberg_three_sixteenths`). Restriction to `Γ(4)` covers the levels `1, 2`
(`selberg_three_sixteenths_all`). The proof uses no spectral theorem.
-/

namespace GaloisForLFunctions.RHTower.SelbergThreeSixteenths
open GaloisForLFunctions.RHTower.SelbergPoincare GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation GaloisForLFunctions.RHTower.SelbergPoincarePole
  GaloisForLFunctions.RHTower.SarnakXuePretrace GaloisForLFunctions.RHTower.SelbergPoincarePairing
  GaloisForLFunctions.RHTower.SelbergMaassFourier GaloisForLFunctions.RHTower.SelbergMaassMean
open _root_.RHTower GaloisForLFunctions.RHTower

theorem norm_le_of_asymp {s₀ C : ℝ} {α : ℂ} (hs₀ : 1 / 2 ≤ s₀) {a : ℝ → ℂ}
    (hE : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀) :
    ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ (‖α‖ + C) * y ^ (1 - s₀) := by
  intro y hy
  have hy0 := hy.1
  have hle : y ^ s₀ ≤ y ^ (1 - s₀) := Real.rpow_le_rpow_of_exponent_ge hy0 hy.2 (by linarith)
  have h1 := hE y hy
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans h1
    exact nonneg_of_mul_nonneg_left this (Real.rpow_pos_of_pos hy0 _)
  have h2 : ‖α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ = ‖α‖ * y ^ (1 - s₀) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy0.le _)]
  calc ‖a y‖ = ‖(a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)) + α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ := by ring_nf
    _ ≤ C * y ^ s₀ + ‖α‖ * y ^ (1 - s₀) := (norm_add_le _ _).trans (by rw [h2]; linarith)
    _ ≤ C * y ^ (1 - s₀) + ‖α‖ * y ^ (1 - s₀) := by gcongr
    _ = _ := by ring

/-- **The leading coefficient vanishes.** For `N ≥ 3`, `m ≥ 1`, `3/4 < s₀ < 1` and a continuous bounded
`Γ(N)`-invariant `g` with cusp-integrable weight, if the `(-m)`-th Fourier coefficient of `g` is
`α y^{1-s₀} + O(y^{s₀})` at `0`, then `α = 0`: the unfolded pairing `N ∫ y^{s-2} e^{-2πmy/N} a(y) dy` would have a pole
at `s₀`, while it equals `∫_{cellP} Q_m(·,s) g`, holomorphic on `Re s > 3/4`. -/
theorem alpha_zero_of_pairing (M : ℕ) [NeZero M] (hM : 3 ≤ M) {m : ℕ} (hm : 1 ≤ m) {s₀ : ℝ}
    (hs₀ : 3 / 4 < s₀) (hs₀1 : s₀ < 1) {g : ℍ → ℂ} (hgc : Continuous g) {B : ℝ} (hgb : ∀ z, ‖g z‖ ≤ B)
    (hg : ∀ (γ : CongruenceSubgroup.Gamma M) z, g ((γ : SL(2, ℤ)) • z) = g z)
    (hgi : IntegrableOn (fun z : ℍ => (z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) * ‖g z‖) (cellP M) volume)
    {α : ℂ} {C : ℝ}
    (hE : ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖coefficient M (-(m : ℤ)) (g ∘ ofComplex) y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀)
    (hcont : ContinuousOn (coefficient M (-(m : ℤ)) (g ∘ ofComplex)) (Ioi 0)) : α = 0 := by
  set a := coefficient M (-(m : ℤ)) (g ∘ ofComplex)
  set c : ℝ := 2 * Real.pi * m / M
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 0 < c := by positivity
  have hm0 : m ≠ 0 := by omega
  have haB : ∀ y, 0 < y → ‖a y‖ ≤ B := by
    intro y hy
    have hb : ∀ x ∈ uIoc (0 : ℝ) (M : ℝ), ‖(g ∘ ofComplex) (point x y)‖ ≤ B := by
      intro x _
      have hp : 0 < (point x y).im := by simpa [point] using hy
      simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hp] using hgb ⟨point x y, hp⟩
    simpa only [a, coefficient] using _root_.RHTower.deningerFourierCoeff_norm_le hMpos hb (-(m : ℤ))
  have hA := norm_le_of_asymp (show (1 : ℝ) / 2 ≤ s₀ by linarith) hE
  set f1 : ℂ → ℂ := fun s => ∫ z in cellP M, Q M m s z * g z
  set f2 : ℂ → ℂ := fun s => (M : ℂ) * mel c a s
  set V : Set ℂ := {s | s₀ < s.re} ∩ {s | s.re < 3}
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hgm : Measurable g := hgc.measurable
  have hf1 : AnalyticOnNhd ℂ f1 V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro s hs
    have h1 : s₀ < s.re := hs.1
    have h2 : s.re < 3 := hs.2
    exact (differentiableAt_pairing M m hm0 hgm hgi (by linarith) h2).differentiableWithinAt
  have hf2 : AnalyticOnNhd ℂ f2 V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro s hs
    exact ((differentiableAt_mel hc hcont hA haB hs.1).const_mul _).differentiableWithinAt
  have hVc : IsPreconnected V :=
    ((convex_halfSpace_re_gt s₀).inter (convex_halfSpace_re_lt 3)).isPreconnected
  have h2V : (2 : ℂ) ∈ V := ⟨by simp; linarith, by simp; norm_num⟩
  have hagree : ∀ s : ℂ, 1 < s.re → f1 s = f2 s := by
    intro s hs
    simp only [f1, f2]
    have hPQ : ∀ z, Q M m s z * g z = poincare M m s z * g z := fun z => by
      rw [poincare_eq_Q M m hM hs z]
    simp_rw [hPQ]
    rw [poincare_pairing M hM hm hs hgc hgb hg]
    congr 1
    unfold mel
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    simp only [a, c]
    rw [Complex.ofReal_exp]
    congr 3
    push_cast; ring
  have hev : f1 =ᶠ[𝓝 2] f2 := by
    have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [this] with s hs
    exact hagree s hs
  have heq := hf1.eqOn_of_preconnected_of_eventuallyEq hf2 hVc h2V hev
  -- continuity of `f1` at `s₀`
  have hcont1 : ContinuousAt f1 (s₀ : ℂ) :=
    (differentiableAt_pairing M m hm0 hgm hgi (by simp; linarith) (by simp; linarith)).continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont1 1 one_pos
  set δ' := min δ (3 - s₀)
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
  refine alpha_eq_zero hc (by linarith) hs₀1 hcont hE haB hδ'0
    (K := (‖f1 s₀‖ + 1) / M) (fun s hs hsδ => ?_)
  have hsV : (s : ℂ) ∈ V := by
    have := min_le_right δ (3 - s₀)
    refine ⟨?_, ?_⟩
    · show s₀ < (s : ℂ).re; rw [Complex.ofReal_re]; exact hs
    · show (s : ℂ).re < 3; rw [Complex.ofReal_re]; linarith
  have h1 : dist (s : ℂ) (s₀ : ℂ) < δ := by
    rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have := min_le_left δ (3 - s₀); linarith
  have h2 := hδ' h1
  rw [dist_eq_norm] at h2
  have h3 : ‖f1 s‖ ≤ ‖f1 s₀‖ + 1 := by
    have := norm_le_insert' (f1 s) (f1 s₀)
    linarith [norm_sub_rev (f1 s) (f1 s₀)]
  rw [heq hsV] at h3
  simp only [f2] at h3
  rw [norm_mul, Complex.norm_natCast] at h3
  rw [le_div_iff₀ hMpos]; linarith [mul_comm (M : ℝ) ‖mel c a s‖]

theorem coefficient_conj (w : ℝ) (hw : 0 ≤ w) (n : ℤ) (F : ℂ → ℂ) (y : ℝ) :
    coefficient w (-n) (fun z => (starRingEnd ℂ) (F z)) y = (starRingEnd ℂ) (coefficient w n F y) := by
  unfold coefficient _root_.RHTower.deningerFourierCoeff
  rw [intervalIntegral.integral_of_le hw, intervalIntegral.integral_of_le hw, map_mul, ← integral_conj]
  congr 1
  · simp
  · apply congrArg; funext x
    rw [map_mul]
    congr 1
    unfold _root_.RHTower.deningerFourierKernel
    rw [← Complex.exp_conj]
    congr 1
    have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by simp [map_ofNat]
    simp [map_div₀, Complex.conj_ofReal, h2]

theorem integral_action (g : SL(2, ℤ)) (z : ℍ) : integralSL2ToReal g • z = g • z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  rfl

open GaloisForLFunctions.RHTower.SelbergMaassExpDecayCell GaloisForLFunctions.RHTower.SelbergModalEnergy in
/-- **Selberg's `3/16` theorem for principal congruence subgroups.** For `N ≥ 2`, the group `Γ(N+1)` has no
Maass cusp form with Laplace eigenvalue `0 < λ < 3/16`. -/
theorem selberg_three_sixteenths (N : ℕ) (hN : 2 ≤ N) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 3 / 16) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) := by
  refine ⟨fun f => ?_⟩
  set M := N + 1
  have hM : 3 ≤ M := by omega
  -- the spectral parameter `s₀ ∈ (3/4, 1)` with `λ = s₀(1 - s₀)`
  set r := Real.sqrt (1 - 4 * lam)
  have hr2 : r ^ 2 = 1 - 4 * lam := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by nlinarith
  have hrh : 1 / 2 < r := by nlinarith
  set s₀ := (1 + r) / 2
  have hs₀ : 3 / 4 < s₀ := by simp only [s₀]; linarith
  have hs₀1 : s₀ < 1 := by simp only [s₀]; linarith
  have hlam : lam = s₀ * (1 - s₀) := by simp only [s₀]; nlinarith
  set lam' : Set.Ioo (0 : ℝ) (1 / 4) := ⟨lam, h0, by linarith⟩
  obtain ⟨B, hB⟩ := GaloisForLFunctions.RHTower.MaassCongruenceL2.source_bounded N f
  have hinv : ∀ (γ : CongruenceSubgroup.Gamma M) z, f.1.1 ((γ : SL(2, ℤ)) • z) = f.1.1 z :=
    fun γ z => by
      have h := f.1.2 ⟨integralSL2ToReal γ, ⟨γ, γ.2, rfl⟩⟩ z
      rwa [show ((⟨integralSL2ToReal γ, ⟨γ, γ.2, rfl⟩⟩ : realImage (CongruenceSubgroup.Gamma (N + 1))) : SL2R) • z =
        (γ : SL(2, ℤ)) • z from integral_action γ z] at h
  have hgi := integrableOn_cellP N lam' f
  -- every nonzero mode vanishes
  have hneg : ∀ m : ℕ, 1 ≤ m → ∀ y, 0 < y → maassCoefficient N f (-(m : ℤ)) y = 0 := by
    intro m hm
    obtain ⟨α, C, hE, hzero⟩ := maassCoefficient_leading N f (by linarith : 1 / 2 < s₀) hs₀1 hlam (-(m : ℤ))
    apply hzero
    exact alpha_zero_of_pairing M hM hm hs₀ hs₀1 (continuous_source f) hB hinv hgi hE
      (GaloisForLFunctions.RHTower.SarnakXueCuspMode.coeff_continuousOn N f _)
  have hposm : ∀ m : ℕ, 1 ≤ m → ∀ y, 0 < y → maassCoefficient N f (m : ℤ) y = 0 := by
    intro m hm
    obtain ⟨α, C, hE, hzero⟩ := maassCoefficient_leading N f (by linarith : 1 / 2 < s₀) hs₀1 hlam (m : ℤ)
    apply hzero
    set g : ℍ → ℂ := fun z => (starRingEnd ℂ) (f.1.1 z)
    have hcoef : ∀ y, coefficient M (-(m : ℤ)) (g ∘ ofComplex) y =
        (starRingEnd ℂ) (maassCoefficient N f (m : ℤ) y) := fun y =>
      coefficient_conj (M : ℝ) (Nat.cast_nonneg _) (m : ℤ) (f.1.1 ∘ ofComplex) y
    have hgc : Continuous g := Complex.continuous_conj.comp (continuous_source f)
    have hgb : ∀ z, ‖g z‖ ≤ B := fun z => by simp only [g, Complex.norm_conj]; exact hB z
    have hgv : ∀ (γ : CongruenceSubgroup.Gamma M) z, g ((γ : SL(2, ℤ)) • z) = g z :=
      fun γ z => by simp only [g, hinv γ z]
    have hgi' : IntegrableOn (fun z : ℍ => (z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) * ‖g z‖)
        (GaloisForLFunctions.RHTower.SarnakXuePretrace.cellP M) volume := by
      simpa only [g, Complex.norm_conj] using hgi
    have hE' : ∀ y ∈ Ioc (0 : ℝ) 1, ‖coefficient M (-(m : ℤ)) (g ∘ ofComplex) y -
        (starRingEnd ℂ) α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀ := by
      intro y hy
      rw [hcoef, ← Complex.conj_ofReal, ← map_mul, ← map_sub, Complex.norm_conj]
      exact hE y hy
    have hcont' : ContinuousOn (coefficient M (-(m : ℤ)) (g ∘ ofComplex)) (Ioi 0) := by
      have : coefficient M (-(m : ℤ)) (g ∘ ofComplex) = fun y => (starRingEnd ℂ) (maassCoefficient N f (m : ℤ) y) :=
        funext hcoef
      rw [this]
      exact Complex.continuous_conj.comp_continuousOn
        (GaloisForLFunctions.RHTower.SarnakXueCuspMode.coeff_continuousOn N f _)
    have h := alpha_zero_of_pairing M hM hm hs₀ hs₀1 hgc hgb hgv hgi' hE' hcont'
    simpa using h
  have hall : ∀ n : ℤ, ∀ y, 0 < y → maassCoefficient N f n y = 0 := by
    intro n y hy
    rcases lt_trichotomy n 0 with hn | hn | hn
    · have := hneg n.natAbs (by omega) y hy
      rwa [show (-(n.natAbs : ℤ)) = n by omega] at this
    · subst hn; exact GaloisForLFunctions.RHTower.SelbergMaassBessel.constant_mode_zero N lam' f hy
    · have := hposm n.natAbs (by omega) y hy
      rwa [show ((n.natAbs : ℤ)) = n by omega] at this
  have hzero : ∀ z : ℍ, f.1.1 z = 0 := by
    intro z
    have h := norm_le_tsum N f z (b := fun _ => (0 : ℝ)) summable_zero
      (fun n => by rw [hall n z.im z.im_pos, norm_zero])
    rw [tsum_zero] at h
    exact norm_le_zero_iff.mp h
  exact f.2.1 (Subtype.ext (funext hzero))

theorem Gamma_le_of_dvd {a b : ℕ} (h : a ∣ b) : CongruenceSubgroup.Gamma b ≤ CongruenceSubgroup.Gamma a := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have e : ∀ {x : ℤ} {v : ZMod b}, (x : ZMod b) = v → (x : ZMod a) = ZMod.castHom h (ZMod a) v :=
    fun hx => by rw [← hx, map_intCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e h1; rwa [map_one] at this
  · have := e h2; rwa [map_zero] at this
  · have := e h3; rwa [map_zero] at this
  · have := e h4; rwa [map_one] at this

/-- Restriction of a Maass cusp form to a smaller subgroup. -/
def restrictMaass {Γ Γ' : Subgroup SL2R} (hle : Γ' ≤ Γ) {lam : ℝ} (f : MaassCuspEigenform Γ lam) :
    MaassCuspEigenform Γ' lam :=
  ⟨⟨f.1.1, fun γ z => f.1.2 ⟨γ, hle γ.2⟩ z⟩, fun h => f.2.1 (by
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this), f.2.2.1, f.2.2.2⟩

/-- **Selberg's `3/16` theorem at every principal congruence level**: for every `N ≥ 1`, `Γ(N)` has no Maass cusp
form with eigenvalue `0 < λ < 3/16`. -/
theorem selberg_three_sixteenths_all (N : ℕ) (hN : 1 ≤ N) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 3 / 16) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma N)) lam) := by
  rcases le_or_gt 3 N with h3 | h3
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    exact selberg_three_sixteenths M (by omega) h0 h1
  · refine ⟨fun f => ?_⟩
    have hdvd : N ∣ 4 := by interval_cases N <;> norm_num
    have hle : realImage (CongruenceSubgroup.Gamma (3 + 1)) ≤ realImage (CongruenceSubgroup.Gamma N) :=
      Subgroup.map_mono (Gamma_le_of_dvd hdvd)
    exact (selberg_three_sixteenths 3 (by norm_num) h0 h1).false (restrictMaass hle f)

/-- **Selberg's `3/16` for every congruence subgroup**: if `Γ ⊇ Γ(N)` for some `N ≥ 1`, then `Γ` has no Maass cusp form
with eigenvalue `0 < λ < 3/16`. -/
theorem selberg_three_sixteenths_congruence {Γ : Subgroup SL(2, ℤ)} {N : ℕ} (hN : 1 ≤ N)
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 3 / 16) :
    IsEmpty (MaassCuspEigenform (realImage Γ) lam) :=
  ⟨fun f => (selberg_three_sixteenths_all N hN h0 h1).false (restrictMaass (Subgroup.map_mono hΓ) f)⟩

end GaloisForLFunctions.RHTower.SelbergThreeSixteenths
