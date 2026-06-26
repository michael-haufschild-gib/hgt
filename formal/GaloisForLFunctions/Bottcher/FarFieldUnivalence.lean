import GaloisForLFunctions.Bottcher.FigureEight
import GaloisForLFunctions.Bottcher.Univalence
import GaloisForLFunctions.Bottcher.BottcherInverse

open Complex Set Filter Topology

namespace Bottcher

/-- **Far-field univalence of the Böttcher coordinate.** For `R` with `2·max(2,‖c‖) < R` and
`16‖c‖ < R²`, `φ_c` is injective on `{ |z| > R }`. In logarithmic coordinates `ζ ↦ z = exp ζ` the
far field is the convex half-plane `{Re ζ > log R}` and `Φ(ζ) := ζ + S(exp ζ)` (with `φ_c = z·exp S`)
has `Re Φ' = 1 + Re(z·S'(z)) ≥ 1 − 16‖c‖/|z|² > 0`, so `Φ` is injective (Noshiro–Warschawski,
`injOn_of_re_deriv_pos`); the `2πi`-periodicity of `Φ` then descends injectivity to `φ_c`. -/
theorem bottcherCoord_injOn_far {c : ℂ} {R : ℝ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    Set.InjOn (bottcherCoord c) {z | R < ‖z‖} := by
  have hcnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hmaxpos : (0:ℝ) < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hRpos : 0 < R := by nlinarith
  set S : ℂ → ℂ := fun w => ∑' k, bottcherLogTerm c w k with hSdef
  have hSan : AnalyticOnNhd ℂ S (escapeOpen c) :=
    (differentiableOn_bottcherLogSum c).analyticOnNhd (isOpen_escapeOpen c)
  have hSderivAn : AnalyticOnNhd ℂ (deriv S) (escapeOpen c) := hSan.deriv
  set Φ : ℂ → ℂ := fun ζ => ζ + S (Complex.exp ζ) with hΦdef
  set H : Set ℂ := {ζ : ℂ | Real.log R < ζ.re} with hHdef
  have hHconv : Convex ℝ H := convex_halfSpace_re_gt _
  -- z = exp ζ is in the escape set, with |z| > R
  have hexpesc : ∀ ζ ∈ H, Complex.exp ζ ∈ escapeOpen c := by
    intro ζ hζ
    have hnorm : R < ‖Complex.exp ζ‖ := by
      rw [Complex.norm_exp]
      have := Real.exp_lt_exp.mpr hζ
      rwa [Real.exp_log hRpos] at this
    show max 2 ‖c‖ < ‖Complex.exp ζ‖
    have : max 2 ‖c‖ < R := by nlinarith [le_max_left 2 ‖c‖]
    linarith
  have hexpnormgt : ∀ ζ ∈ H, R < ‖Complex.exp ζ‖ := by
    intro ζ hζ
    rw [Complex.norm_exp]
    have := Real.exp_lt_exp.mpr hζ
    rwa [Real.exp_log hRpos] at this
  -- derivative of Φ
  have hΦderiv : ∀ ζ ∈ H, HasDerivAt Φ (1 + Complex.exp ζ * deriv S (Complex.exp ζ)) ζ := by
    intro ζ hζ
    have hSd : HasDerivAt S (deriv S (Complex.exp ζ)) (Complex.exp ζ) :=
      (hSan _ (hexpesc ζ hζ)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun ζ => S (Complex.exp ζ))
        (deriv S (Complex.exp ζ) * Complex.exp ζ) ζ :=
      hSd.comp ζ (Complex.hasDerivAt_exp ζ)
    have := (hasDerivAt_id ζ).add hcomp
    simpa [hΦdef, mul_comm] using this
  -- positivity of Re Φ'
  have hpos : ∀ ζ ∈ H, 0 < (deriv Φ ζ).re := by
    intro ζ hζ
    rw [(hΦderiv ζ hζ).deriv]
    set z := Complex.exp ζ with hz
    have hznorm : R < ‖z‖ := hexpnormgt ζ hζ
    have hzpos : 0 < ‖z‖ := lt_trans hRpos hznorm
    have hbd : ‖deriv S z‖ ≤ 16 * ‖c‖ / ‖z‖ ^ 3 :=
      norm_deriv_bottcherLogSum_le (by linarith [hexpnormgt ζ hζ] : 2 * max 2 ‖c‖ < ‖z‖)
    have hwbd : ‖z * deriv S z‖ < 1 := by
      rw [norm_mul]
      have hz3 : (0:ℝ) < ‖z‖ ^ 3 := by positivity
      have hbd' : ‖deriv S z‖ * ‖z‖ ^ 3 ≤ 16 * ‖c‖ := (le_div_iff₀ hz3).mp hbd
      have hzsq : 16 * ‖c‖ < ‖z‖ ^ 2 := by nlinarith [hznorm, hRpos, hR2]
      have hp : ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ := by ring
      nlinarith [hbd', hzsq, hzpos, hp, mul_pos hzpos hzpos, norm_nonneg (deriv S z)]
    have hstrict : -1 < (z * deriv S z).re := by
      have hle := Complex.abs_re_le_norm (z * deriv S z)
      have h2 : |(z * deriv S z).re| < 1 := lt_of_le_of_lt hle hwbd
      rw [abs_lt] at h2; exact h2.1
    simp only [Complex.add_re, Complex.one_re]
    linarith [hstrict]
  -- continuity of Φ'
  have hcont : ContinuousOn (fun ζ => deriv Φ ζ) H := by
    apply ContinuousOn.congr (f := fun ζ => 1 + Complex.exp ζ * deriv S (Complex.exp ζ))
    · apply continuousOn_const.add
      apply Complex.continuous_exp.continuousOn.mul
      exact hSderivAn.continuousOn.comp Complex.continuous_exp.continuousOn hexpesc
    · intro ζ hζ; exact (hΦderiv ζ hζ).deriv
  -- NW: Φ injective on H
  have hΦinj : Set.InjOn Φ H :=
    injOn_of_re_deriv_pos hHconv (fun ζ hζ => (hΦderiv ζ hζ).deriv ▸ hΦderiv ζ hζ) hcont hpos
  -- descent to φ_c
  intro z₁ hz₁ z₂ hz₂ heq
  simp only [mem_setOf_eq] at hz₁ hz₂
  have hz₁0 : z₁ ≠ 0 := fun h => by rw [h, norm_zero] at hz₁; linarith
  have hz₂0 : z₂ ≠ 0 := fun h => by rw [h, norm_zero] at hz₂; linarith
  set ζ₁ := Complex.log z₁ with hζ₁
  set ζ₂ := Complex.log z₂ with hζ₂
  have hζ₁H : ζ₁ ∈ H := by
    show Real.log R < ζ₁.re
    rw [hζ₁, Complex.log_re]; exact Real.log_lt_log hRpos hz₁
  have hζ₂H : ζ₂ ∈ H := by
    show Real.log R < ζ₂.re
    rw [hζ₂, Complex.log_re]; exact Real.log_lt_log hRpos hz₂
  have hexp₁ : Complex.exp ζ₁ = z₁ := Complex.exp_log hz₁0
  have hexp₂ : Complex.exp ζ₂ = z₂ := Complex.exp_log hz₂0
  -- exp(Φ ζᵢ) = φ_c zᵢ
  have hΦexp : ∀ {z : ℂ} {ζ : ℂ} (hz0 : z ≠ 0), Complex.exp ζ = z →
      Complex.exp (Φ ζ) = bottcherCoord c z := by
    intro z ζ hz0 hez
    rw [hΦdef]
    simp only
    rw [Complex.exp_add, hez, bottcherCoord_eq_mul_exp hz0]
  have he1 : Complex.exp (Φ ζ₁) = bottcherCoord c z₁ := hΦexp hz₁0 hexp₁
  have he2 : Complex.exp (Φ ζ₂) = bottcherCoord c z₂ := hΦexp hz₂0 hexp₂
  have hΦeq : Complex.exp (Φ ζ₁) = Complex.exp (Φ ζ₂) := by rw [he1, he2, heq]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hΦeq
  -- Φ(ζ₂ + n·2πi) = Φ ζ₂ + n·2πi = Φ ζ₁
  set ζ₂' := ζ₂ + (n : ℂ) * (2 * ↑Real.pi * Complex.I) with hζ₂'
  have hexp₂' : Complex.exp ζ₂' = z₂ := by
    rw [hζ₂', Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hexp₂]
  have hΦ₂' : Φ ζ₂' = Φ ζ₂ + (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [hΦdef]; simp only; rw [hexp₂', hζ₂', hexp₂]; ring
  have hζ₂'H : ζ₂' ∈ H := by
    show Real.log R < ζ₂'.re
    have : ζ₂'.re = ζ₂.re := by
      rw [hζ₂']; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [this]; exact hζ₂H
  have hΦζ : Φ ζ₁ = Φ ζ₂' := by rw [hΦ₂', hn]
  have hζeq : ζ₁ = ζ₂' := hΦinj hζ₁H hζ₂'H hΦζ
  rw [← hexp₁, ← hexp₂', hζeq]

/-- **Global analytic inverse of `φ_c` on the far field (L3).** With far-field injectivity (L2,
`bottcherCoord_injOn_far`) and the local inverse (`exists_localInverse_bottcherCoord`), the set-theoretic
left inverse `ψ = invFunOn φ_c A` (`A = {|z|>R}`) is analytic at every `φ_c z` (`z ∈ A`), inverts `φ_c`
on `A`, and is a local right inverse. So `φ_c : A → φ_c(A)` is a biholomorphism — the far-field chart the
dyadic-cover deck map is continued inward from. -/
theorem exists_analytic_inverse_far {c : ℂ} {R : ℝ}
    (hR1 : 2 * max 2 ‖c‖ < R) (hR2 : 16 * ‖c‖ < R ^ 2) :
    ∃ ψ : ℂ → ℂ,
      (∀ z, R < ‖z‖ → ψ (bottcherCoord c z) = z) ∧
      (∀ z, R < ‖z‖ → AnalyticAt ℂ ψ (bottcherCoord c z)) ∧
      (∀ z, R < ‖z‖ → ∀ᶠ w in 𝓝 (bottcherCoord c z), bottcherCoord c (ψ w) = w) := by
  classical
  set A : Set ℂ := {z | R < ‖z‖} with hAdef
  have hAsub : A ⊆ escapeOpen c := by
    intro z hz
    show max 2 ‖c‖ < ‖z‖
    have : max 2 ‖c‖ < R := by nlinarith [le_max_left 2 ‖c‖, norm_nonneg c]
    exact lt_trans this hz
  have hinj : Set.InjOn (bottcherCoord c) A := bottcherCoord_injOn_far hR1 hR2
  set ψ : ℂ → ℂ := Function.invFunOn (bottcherCoord c) A with hψdef
  have hleft : ∀ z ∈ A, ψ (bottcherCoord c z) = z := fun z hz =>
    hinj.leftInvOn_invFunOn hz
  refine ⟨ψ, fun z hz => hleft z hz, ?_, ?_⟩
  · intro z₀ hz₀A
    have hz₀ : z₀ ∈ A := hz₀A
    obtain ⟨loc, hlocAn, hlocLeft, hlocRight⟩ := exists_localInverse_bottcherCoord (hAsub hz₀)
    have hlocCont : ContinuousAt loc (bottcherCoord c z₀) := hlocAn.continuousAt
    have hlocAtz₀ : loc (bottcherCoord c z₀) = z₀ := hlocLeft.self_of_nhds
    have hlocInA : ∀ᶠ w in 𝓝 (bottcherCoord c z₀), loc w ∈ A := by
      have hAopen : IsOpen A := isOpen_lt continuous_const continuous_norm
      have hAn : A ∈ 𝓝 z₀ := hAopen.mem_nhds hz₀
      exact hlocCont.preimage_mem_nhds (by rwa [hlocAtz₀])
    have hagree : ψ =ᶠ[𝓝 (bottcherCoord c z₀)] loc := by
      filter_upwards [hlocInA, hlocRight] with w hwA hwRight
      have hex : ∃ a ∈ A, bottcherCoord c a = w := ⟨loc w, hwA, hwRight⟩
      have hψw : bottcherCoord c (ψ w) = w := Function.invFunOn_eq hex
      have hψwA : ψ w ∈ A := Function.invFunOn_mem hex
      exact hinj hψwA hwA (by rw [hψw, hwRight])
    exact hlocAn.congr hagree.symm
  · intro z₀ hz₀A
    have hz₀ : z₀ ∈ A := hz₀A
    obtain ⟨loc, hlocAn, hlocLeft, hlocRight⟩ := exists_localInverse_bottcherCoord (hAsub hz₀)
    have hlocCont : ContinuousAt loc (bottcherCoord c z₀) := hlocAn.continuousAt
    have hlocAtz₀ : loc (bottcherCoord c z₀) = z₀ := hlocLeft.self_of_nhds
    have hlocInA : ∀ᶠ w in 𝓝 (bottcherCoord c z₀), loc w ∈ A := by
      have hAopen : IsOpen A := isOpen_lt continuous_const continuous_norm
      have hAn : A ∈ 𝓝 z₀ := hAopen.mem_nhds hz₀
      exact hlocCont.preimage_mem_nhds (by rwa [hlocAtz₀])
    filter_upwards [hlocInA, hlocRight] with w hwA hwRight
    have hex : ∃ a ∈ A, bottcherCoord c a = w := ⟨loc w, hwA, hwRight⟩
    exact Function.invFunOn_eq hex

end Bottcher
