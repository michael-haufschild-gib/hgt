import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheCriticalConservationLaw
import GaloisForLFunctions.RHTower.ReflectionParity

/-!
# The Quantization of the Square-Root Surplus

A positive deformation of the height-coupled carrier `ζ_γ` adds a nonnegative prime-side measure `ν`.
On the scale `√x` its size is the Abel residue `lim_{σ↓½} (σ − ½) 𝓛ν(σ)`. The Abel limit theorem
identifies this residue with the drop of the central vanishing order, and the functional equation
makes central orders even. Hence the square-root mass that positivity can add is quantized.

* **Quantization (`tendsto_abel_excess_eq_centralDrop`).** If `ξ` has no off-critical zero at ordinate
  `γ`, the residue `(σ − ½) 𝓛ν(σ)` of a (perturbed) positive deformation converges, and its limit is an
  even integer `D` with `0 ≤ D ≤ 2 ord_{½+iγ} ξ`. In particular it vanishes unless `½ + iγ` is a zero
  of `ξ`.
* **Arithmetic form (`tendsto_surplus_residue_eq_centralDrop`).** For an arithmetic member
  `−F'/F = Σ b(n) n^{−s}` whose deficit against `b_γ` has zero Abel residue at `½`, the surplus prime
  mass satisfies `(σ − ½) Σ_{n ≥ 2} (b(n) − b_γ(n))⁺ n^{−σ} → D` with `D ∈ 2ℕ` (the series is the
  Laplace transform of the surplus measure `Σ s(n) δ_{log n}`, `laplace_latticeMeasure`),
  `D ≤ 2 ord_{½+iγ} ξ`: surplus prime mass at the square-root scale,
  `Σ_{n ≤ x} (b(n) − b_γ(n))⁺ ≈ 2D √x` in the Abel sense, comes in even integer units bounded by the
  multiplicity of the critical zero at height `γ`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace complexLaplace_ofReal)

/-- The central vanishing order of a member of the height-coupled class is even: `Λ` is symmetric
under `s ↦ 1 − s`, whose fixed point is `½`. -/
theorem even_centralOrder_of_heightCoupled {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) : Even (analyticOrderAt Λ (1 / 2)).toNat :=
  RHTower.analyticOrderAt_even_of_reflection hHC.analyticOnNhd_univ
    (fun s => by rw [show 2 * (1 / 2 : ℂ) - s = 1 - s by ring]; exact hHC.sym_Λ s)
    (hHC.orderAt_ne_top _)

/-- `ord_{½} Λ_γ = 2 ord_{½+iγ} ξ`. -/
theorem centralOrder_heightCoupledΛ (γ : ℝ) :
    (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat =
      2 * (analyticOrderAt (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I)).toNat := by
  have hZ := completedPositiveSystem_riemannZeta
  have h := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hZ γ (1 / 2)
  have hhalf : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  rw [hhalf] at h
  have hξ : (fun s => 2 * RHTower.xi s) (1 / 2) ≠ 0 :=
    mul_ne_zero two_ne_zero (by simpa using RHTower.xi_ne_zero_of_real (1 / 2))
  rw [h, (hZ.entire_Λ.analyticAt _).analyticOrderAt_eq_zero.mpr hξ]
  simp

/-- From the Abel limit of the excess on the real axis: the limit is the central drop, a
nonnegative even integer at most `2 ord_{½+iγ} ξ`. -/
theorem quantization_of_tendsto {γ : ℝ} {F Λ : ℂ → ℂ} (hHC : HeightCoupledSystem 2 1 1 γ F Λ)
    {f : ℝ → ℝ} (hf : ∀ σ : ℝ, 1 / 2 < σ → 0 ≤ f σ)
    (hlim : Tendsto f (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat : ℝ) -
        (analyticOrderAt Λ (1 / 2)).toNat))) :
    Tendsto f (𝓝[>] (1 / 2 : ℝ))
        (𝓝 (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
          (analyticOrderAt Λ (1 / 2)).toNat : ℕ) : ℝ)) ∧
      Even ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
        (analyticOrderAt Λ (1 / 2)).toNat) ∧
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
          (analyticOrderAt Λ (1 / 2)).toNat ≤
        2 * (analyticOrderAt (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I)).toNat := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set k := (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat
  set a := (analyticOrderAt Λ (1 / 2)).toNat
  -- the limit of nonnegative quantities is nonnegative: no central excess
  have hak : a ≤ k := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) - a :=
      ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun σ hσ => hf σ hσ)
    exact_mod_cast (sub_nonneg.mp h0)
  refine ⟨by rwa [Nat.cast_sub hak], ?_, ?_⟩
  · exact (even_centralOrder_of_heightCoupled hHC0).tsub (even_centralOrder_of_heightCoupled hHC)
  · rw [← centralOrder_heightCoupledΛ γ]
    exact Nat.sub_le k a

/-- **Quantization of the square-root excess.** If `ξ` has no off-critical zero at ordinate `γ` and
`(F, Λ)` is a perturbed positive deformation of `ζ_γ` (`−F'/F + ζ_γ'/ζ_γ = 𝓛ν + E`, `ν ≥ 0`, `E`
holomorphic on `Re s > σ_E`, `σ_E < ½`), then `(σ − ½) 𝓛ν(σ)` converges as `σ ↓ ½` to the central
drop `D = ord_{½} Λ_γ − ord_{½} Λ`, an even natural number with `D ≤ 2 ord_{½+iγ} ξ`. -/
theorem tendsto_abel_excess_eq_centralDrop {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    Tendsto (fun σ : ℝ => (σ - 1 / 2) * laplaceReal ν σ) (𝓝[>] (1 / 2 : ℝ))
        (𝓝 (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
          (analyticOrderAt Λ (1 / 2)).toNat : ℕ) : ℝ)) ∧
      Even ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
        (analyticOrderAt Λ (1 / 2)).toNat) ∧
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
          (analyticOrderAt Λ (1 / 2)).toNat ≤
        2 * (analyticOrderAt (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I)).toNat := by
  have h := tendsto_abel_complexLaplace hoff hHC hconv hσE hE hagree 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  have hr := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, complexLaplace_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.sub_re, Complex.natCast_re] at hr
  refine quantization_of_tendsto hHC (fun σ hσ => mul_nonneg (by linarith)
    (setIntegral_nonneg measurableSet_Ioi fun u _ => (Real.exp_pos _).le)) hr

/-- **Quantization of the square-root surplus of arithmetic members.** If `ξ` has no off-critical
zero at ordinate `γ` and an arithmetic member of `HeightCoupledSystem 2 1 1 γ` has a deficit series
converging on `Re s > ½` with zero Abel residue at `½`, then the surplus residue
`(σ − ½) Σ_{n ≥ 2} (b(n) − b_γ(n))⁺ n^{−σ}` converges to the central drop, an even natural number at
most `2 ord_{½+iγ} ξ`. -/
theorem tendsto_surplus_residue_eq_centralDrop {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv (fun n => (latticeDeficit γ b n : ℂ)) ≤ (1 / 2 : ℝ))
    (hres : Tendsto (fun σ : ℝ => (σ - 1 / 2) *
      (LSeries (fun n => (latticeDeficit γ b n : ℂ)) (σ : ℂ)).re) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0)) :
    Tendsto (fun σ : ℝ => (σ - 1 / 2) * laplaceReal (latticeMeasure (latticeSurplus γ b)) σ)
        (𝓝[>] (1 / 2 : ℝ))
        (𝓝 (((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
          (analyticOrderAt Λ (1 / 2)).toNat : ℕ) : ℝ)) ∧
      Even ((analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
        (analyticOrderAt Λ (1 / 2)).toNat) ∧
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat -
          (analyticOrderAt Λ (1 / 2)).toNat ≤
        2 * (analyticOrderAt (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I)).toNat := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set D : ℂ → ℂ := LSeries (fun n => (latticeDeficit γ b n : ℂ)) with hDdef
  have hE : DifferentiableOn ℂ (fun s => (b 1 : ℂ) - D s) {s : ℂ | (1 / 2 : ℝ) < s.re} :=
    fun s hs => ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_of_le_of_lt hdef
      (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt).differentiableWithinAt
  obtain ⟨hmass, hsplit⟩ := latticeMember_primeMass_split (γ := γ) hb habs hL
  obtain ⟨c, -, -, hanchor, hrel, -⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hmass hE hsplit
  have hc : c ≤ 1 / 2 := by
    by_contra hgt
    push Not at hgt
    have hz := (hanchor (by linarith) hgt).1
    have := hoff c (xi_add_eq_zero_of_heightCoupledΛ_real_zero hz)
    linarith
  have hmax : max c (1 / 2 : ℝ) = 1 / 2 := max_eq_right hc
  -- the perturbation `b(1) − D` is Abel-negligible at the centre
  have hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - (1 / 2 : ℝ) : ℝ) : ℂ) *
      ((b 1 : ℂ) - D ((σ : ℂ) + (t : ℂ) * I))) (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
    intro t
    have h1 : Tendsto (fun σ : ℝ => ((σ - 1 / 2 : ℝ) : ℂ) * (b 1 : ℂ)) (𝓝[>] (1 / 2 : ℝ))
        (𝓝 0) := by
      have h : Continuous fun σ : ℝ => ((σ - 1 / 2 : ℝ) : ℂ) * (b 1 : ℂ) := by fun_prop
      have h' := (h.tendsto (1 / 2 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (1 / 2 : ℝ)))
      simpa using h'
    have h2 := tendsto_sub_mul_LSeries_of_residue_zero (latticeDeficit_nonneg γ b) hdef hres t
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3.congr fun σ => by simp only [hDdef]; ring
  have h := tendsto_abel_of_rel hHC.entire_Λ hHC0.entire_Λ hHC.orderAt_ne_top
    hHC0.orderAt_ne_top (x₀ := 1 / 2) (fun z hz => hrel z (by rw [hmax]; exact hz)) hEt 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero,
    show (((1 / 2 : ℝ)) : ℂ) = 1 / 2 by norm_num] at h
  have hr := (Complex.continuous_re.tendsto _).comp h
  simp only [Function.comp_def, complexLaplace_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.sub_re, Complex.natCast_re] at hr
  exact quantization_of_tendsto hHC (fun σ hσ => mul_nonneg (by linarith)
    (setIntegral_nonneg measurableSet_Ioi fun u _ => (Real.exp_pos _).le)) hr

end GaloisForLFunctions.BiarithmeticGaugeGeometry
