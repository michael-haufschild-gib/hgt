import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergContinuation
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# The mean-square law of the cusp modes

For a cusp form `g` of the modular horizon with eigenvalue `λ = ¼ + t²` and Whittaker coefficients `ρ(n)`,

  `(1/N) Σ_{|n|<N} |ρ(n)|² → (24/π²) cosh(πt) ‖g‖²`,   `‖g‖² = ∫_𝒟 |g|² dμ`

(`tendsto_mean_square`): every horocyclic harmonic of a ringdown mode carries on average the same energy, and
that energy is the `L²` norm of the mode times the thermal factor `cosh(πt) = π/|Γ(½+it)|²`.

**Proof.** The completed Rankin–Selberg function `Λ_g(s) = ∫_𝒟 |g|² E*(s-½)` has its only pole on `Re s > ½`
at `s = 1`, coming from the constant term `ξ(2u) Y^{½-u}/(2u(2u-1))` of `E*(u)` at `u = ½`. Multiplying by
`s - 1` removes it: `(u - ½) E*(u)` is an Eisenstein-type function `A₁(u) Y^{½+u} + A₂(u) Y^{½-u} + A₃(u) T(u)`
with coefficients holomorphic at `u = ½`, so `F_g(s) = (s - 1) Λ_g(s)` is holomorphic on `ℂ ∖ {0, ½}` by the same
cusp domination (`differentiableOn_integral_shape`), and `F_g(1) = ¼ ‖g‖²` since `(u - ½)E*(u) → ξ(1)/2 = ¼`.
With `c(s)` the Gamma–zeta factor, `φ = F_g/c` is holomorphic on `Re s > ½` and `φ(s)/(s - 1)` is the
Rankin–Selberg Dirichlet series `Σ_m (|ρ(m)|² + |ρ(-m)|²) m^{-s}` on `Re s > 1`; the slope of `φ` at `1` is the
continuous extension of that series minus `φ(1)/(s - 1)` to `Re s ≥ 1`. The Wiener–Ikehara theorem converts
this into the asymptotic, and `φ(1) = (¼‖g‖²)/c(1)` with
`c(1) = ξ(2)/2 · (2π)^{-1} · ¼ Γ(½)² Γ(½+it)Γ(½-it) = π²/(96 cosh πt)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspMS

open HeckeCusp CuspL CuspRSC

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-! ### Eisenstein-type functions -/

/-- An Eisenstein-type function `A₁(u) Y^{½+u} + A₂(u) Y^{½-u} + A₃(u) T(u; x, Y)`, `T` the Whittaker tail. -/
def shape (A₁ A₂ A₃ : ℂ → ℂ) (u : ℂ) (x Y : ℝ) : ℂ :=
  A₁ u * (Y : ℂ) ^ (1 / 2 + u) + A₂ u * (Y : ℂ) ^ (1 / 2 - u) + A₃ u * eisTail u x Y

/-- **Polynomial bound for `Y ≥ ½`, uniform on a compact set where the coefficients are continuous.** -/
theorem exists_shape_bound {A₁ A₂ A₃ : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (h₁ : ContinuousOn A₁ K) (h₂ : ContinuousOn A₂ K) (h₃ : ContinuousOn A₃ K) :
    ∃ α β a : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ a ∧ ∀ u ∈ K, ∀ (x Y : ℝ), 1 / 2 ≤ Y →
      ‖shape A₁ A₂ A₃ u x Y‖ ≤ α * Y ^ a + β := by
  rcases K.eq_empty_or_nonempty with hE | hne
  · exact ⟨0, 0, 0, le_rfl, le_rfl, le_rfl, fun u hu => by simp [hE] at hu⟩
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (Complex.continuous_re.continuousOn (s := K))
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ hne.some_mem)
  obtain ⟨K₁, hK₁⟩ := hK.exists_bound_of_continuousOn h₁
  obtain ⟨K₂, hK₂⟩ := hK.exists_bound_of_continuousOn h₂
  obtain ⟨K₃, hK₃⟩ := hK.exists_bound_of_continuousOn h₃
  have hK₁0 : 0 ≤ K₁ := (norm_nonneg _).trans (hK₁ _ hne.some_mem)
  have hK₂0 : 0 ≤ K₂ := (norm_nonneg _).trans (hK₂ _ hne.some_mem)
  have hK₃0 : 0 ≤ K₃ := (norm_nonneg _).trans (hK₃ _ hne.some_mem)
  obtain ⟨Ct, hCt0, hCt⟩ := norm_weightedTail_le hA0
  set a := A + 1 / 2
  refine ⟨K₁ + K₂, (K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct), a, by positivity, by positivity,
    by positivity, fun u hu x Y hY => ?_⟩
  have hre : |u.re| ≤ A := by simpa [Real.norm_eq_abs] using hA u hu
  have hre' := abs_le.1 hre
  have hw1 : |(1 / 2 + u).re| ≤ a := by
    have : (1 / 2 + u).re = 1 / 2 + u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hw2 : |(1 / 2 - u).re| ≤ a := by
    have : (1 / 2 - u).re = 1 / 2 - u.re := by simp
    rw [this, abs_le]; simp only [a]; constructor <;> linarith
  have hP1 := norm_cpow_le hY (by positivity) hw1
  have hP2 := norm_cpow_le hY (by positivity) hw2
  have hT : ‖eisTail u x Y‖ ≤ 2 * Ct := by
    unfold eisTail
    refine (norm_add_le _ _).trans ?_
    linarith [hCt u false x Y hre hY, hCt u true x Y hre hY]
  have e1 : ‖A₁ u * (Y : ℂ) ^ (1 / 2 + u)‖ ≤ K₁ * (Y ^ a + 2 ^ a) := by
    rw [norm_mul]; exact mul_le_mul (hK₁ u hu) hP1 (norm_nonneg _) hK₁0
  have e2 : ‖A₂ u * (Y : ℂ) ^ (1 / 2 - u)‖ ≤ K₂ * (Y ^ a + 2 ^ a) := by
    rw [norm_mul]; exact mul_le_mul (hK₂ u hu) hP2 (norm_nonneg _) hK₂0
  have e3 : ‖A₃ u * eisTail u x Y‖ ≤ K₃ * (2 * Ct) := by
    rw [norm_mul]; exact mul_le_mul (hK₃ u hu) hT (norm_nonneg _) hK₃0
  unfold shape
  calc _ ≤ ‖A₁ u * (Y : ℂ) ^ (1 / 2 + u)‖ + ‖A₂ u * (Y : ℂ) ^ (1 / 2 - u)‖ +
        ‖A₃ u * eisTail u x Y‖ := norm_add₃_le
    _ ≤ K₁ * (Y ^ a + 2 ^ a) + K₂ * (Y ^ a + 2 ^ a) + K₃ * (2 * Ct) := by linarith
    _ = (K₁ + K₂) * Y ^ a + ((K₁ + K₂) * 2 ^ a + K₃ * (2 * Ct)) := by ring

theorem continuous_shape_max (A₁ A₂ A₃ : ℂ → ℂ) (u : ℂ) :
    Continuous fun z : ℍ => shape A₁ A₂ A₃ u z.re (max z.im (1 / 2)) := by
  have hY : Continuous fun z : ℍ => max z.im (1 / 2) :=
    UpperHalfPlane.continuous_im.max continuous_const
  have hpos : ∀ z : ℍ, 0 < max z.im (1 / 2) := fun z => lt_max_of_lt_right (by norm_num)
  have hcp : ∀ w : ℂ, Continuous fun z : ℍ => ((max z.im (1 / 2) : ℝ) : ℂ) ^ w := fun w =>
    continuous_iff_continuousAt.2 fun z =>
      (continuousAt_cpow_const (ofReal_mem_slitPlane.2 (hpos z))).comp
        (f := fun z : ℍ => ((max z.im (1 / 2) : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hY).continuousAt
  unfold shape eisTail
  exact ((continuous_const.mul (hcp _)).add (continuous_const.mul (hcp _))).add
    (continuous_const.mul ((continuous_weightedTail_max u false).add (continuous_weightedTail_max u true)))

theorem differentiableAt_shape {A₁ A₂ A₃ : ℂ → ℂ} {u : ℂ} (h₁ : DifferentiableAt ℂ A₁ u)
    (h₂ : DifferentiableAt ℂ A₂ u) (h₃ : DifferentiableAt ℂ A₃ u) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableAt ℂ (fun v => shape A₁ A₂ A₃ v x Y) u := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have e1 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 + v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 + v) u).const_cpow (Or.inl hYC)
  have e2 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 - v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 - v) u).const_cpow (Or.inl hYC)
  exact ((h₁.mul e1).add (h₂.mul e2)).add (h₃.mul (differentiableAt_eisTail x hY u))

/-- **`u ↦ ∫_𝒟 |g|² Φ(u)` is holomorphic wherever the coefficients of the Eisenstein-type `Φ` are.** -/
theorem differentiableOn_integral_shape (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {A₁ A₂ A₃ : ℂ → ℂ} {V : Set ℂ}
    (hV : IsOpen V) (h₁ : DifferentiableOn ℂ A₁ V) (h₂ : DifferentiableOn ℂ A₂ V)
    (h₃ : DifferentiableOn ℂ A₃ V) :
    DifferentiableOn ℂ (fun u => ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) *
      shape A₁ A₂ A₃ u z.re z.im) V := by
  set F : ℍ → ℂ → ℂ := fun z u => ModularGroup.fd.indicator
    (fun w => ((‖g w‖ ^ 2 : ℝ) : ℂ) * shape A₁ A₂ A₃ u w.re w.im) z
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  have hF : ∀ z, DifferentiableOn ℂ (F z) V := by
    intro z
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [F, indicator_of_mem hz]
      intro u hu
      have hVu := hV.mem_nhds hu
      exact ((differentiableAt_const _).mul (differentiableAt_shape ((h₁ u hu).differentiableAt hVu)
        ((h₂ u hu).differentiableAt hVu) ((h₃ u hu).differentiableAt hVu) z.re
          z.im_pos)).differentiableWithinAt
    · simp only [F, indicator_of_notMem hz]
      exact differentiableOn_const _
  have hmeas : ∀ u ∈ V, AEStronglyMeasurable (fun z => F z u) volume := by
    intro u _
    have hc : Continuous fun w : ℍ => ((‖g w‖ ^ 2 : ℝ) : ℂ) *
        shape A₁ A₂ A₃ u w.re (max w.im (1 / 2)) :=
      (Complex.continuous_ofReal.comp ((continuous_of_maass hg.2.1).norm.pow 2)).mul
        (continuous_shape_max _ _ _ _)
    refine (hc.aestronglyMeasurable.indicator hfd).congr (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ ModularGroup.fd
    · simp only [F, indicator_of_mem hz, max_eq_left (half_lt_im_of_mem_fd hz).le]
    · simp only [F, indicator_of_notMem hz]
  refine (RHTower.differentiableOn_integral_of_locally_bounded hV hF hmeas fun u₀ hu₀ => ?_).congr
    fun u _ => (integral_indicator hfd).symm
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hV u₀ hu₀
  have hsub : Metric.closedBall u₀ (r / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrV
  refine ⟨r / 2, by positivity, hsub, ?_⟩
  obtain ⟨α, β, a, hα, hβ, ha, hb⟩ := exists_shape_bound (isCompact_closedBall u₀ (r / 2))
    (h₁.continuousOn.mono hsub) (h₂.continuousOn.mono hsub) (h₃.continuousOn.mono hsub)
  obtain ⟨B, hB⟩ := exists_bound_on_fd hg hρ0 hρ hα hβ ha
  refine ⟨ModularGroup.fd.indicator (fun z => ‖g z‖ ^ 2 * (α * z.im ^ a + β)), ?_, fun z u hu => ?_⟩
  · have hvol : volume ModularGroup.fd ≠ ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_ne_top
    refine (integrable_indicator_iff hfd).2 (Measure.integrableOn_of_bounded (M := B) hvol ?_ ?_)
    · exact ((((continuous_of_maass hg.2.1).norm.pow 2).mul
        ((continuous_const.mul (UpperHalfPlane.continuous_im.rpow_const fun z =>
          Or.inl (ne_of_gt z.im_pos))).add continuous_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hfd] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := z.im_pos; positivity)]
      exact hB z hz
  · by_cases hz : z ∈ ModularGroup.fd
    · simp only [F, indicator_of_mem hz]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hb u hu z.re z.im (half_lt_im_of_mem_fd hz).le) (sq_nonneg _)
    · simp only [F, indicator_of_notMem hz, norm_zero, le_refl]

/-! ### Removing the pole at `s = 1` -/

/-- Coefficients of `(u - ½) E*(u)`: `(u-½)ξ(1+2u)/((1+2u)2u)`, `ξ(2u)/(4u)`, `u - ½`. -/
def resA₁ (u : ℂ) : ℂ := (u - 1 / 2) * xi (1 + 2 * u) / ((1 + 2 * u) * (2 * u))
def resA₂ (u : ℂ) : ℂ := xi (2 * u) / (4 * u)
def resA₃ (u : ℂ) : ℂ := u - 1 / 2

theorem shape_res_eq {u : ℂ} (hu : u ≠ 1 / 2) (h0 : u ≠ 0) (hm : u ≠ -(1 / 2)) (x Y : ℝ) :
    shape resA₁ resA₂ resA₃ u x Y = (u - 1 / 2) * EisAuto.completedEisenstein u x Y := by
  unfold shape resA₁ resA₂ resA₃ EisAuto.completedEisenstein eisensteinNumerator
  have ha : (1 + 2 * u) * (1 + 2 * u)⁻¹ = 1 :=
    mul_inv_cancel₀ fun h => hm (by linear_combination h / 2)
  have hb : (2 * u - 1) * (2 * u - 1)⁻¹ = 1 := mul_inv_cancel₀ fun h => hu (by linear_combination h / 2)
  have hc : u * u⁻¹ = 1 := mul_inv_cancel₀ h0
  generalize (Y : ℂ) ^ (1 / 2 - u) = Q
  generalize (Y : ℂ) ^ (1 / 2 + u) = P
  generalize eisTail u x Y = T
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-((u - 1 / 2) * (2 * u - 1)⁻¹ * xi (2 * u) * Q * u⁻¹ / 2 +
      (u - 1 / 2) * T * u * u⁻¹)) * ha + (-(xi (2 * u) * Q * u⁻¹ / 4)) * hb + (-((u - 1 / 2) * T)) * hc

/-- At `u = ½` the regularized function is the constant `ξ(1)/2 = ¼`. -/
theorem shape_res_half (x Y : ℝ) : shape resA₁ resA₂ resA₃ (1 / 2) x Y = 1 / 4 := by
  unfold shape resA₁ resA₂ resA₃
  have e : xi (2 * (1 / 2 : ℂ)) = 1 / 2 := by
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num]; unfold xi; ring
  simp only [sub_self, cpow_zero]
  rw [e]
  ring

/-- `F_g(s) = ∫_𝒟 |g|² (s - 1) E*(s - ½)`, the completed Rankin–Selberg function with its pole removed. -/
def residueRS (g : UpperHalfPlane → ℂ) (s : ℂ) : ℂ :=
  ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * shape resA₁ resA₂ resA₃ (s - 1 / 2) z.re z.im

/-- **`F_g` is holomorphic on `ℂ ∖ {0, ½}`, across `s = 1`.** -/
theorem differentiableOn_residueRS (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    DifferentiableOn ℂ (residueRS g) ({0, 1 / 2} : Set ℂ)ᶜ := by
  have hV : IsOpen (({0, -(1 / 2)} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  have hmem : ∀ {u : ℂ}, u ∈ (({0, -(1 / 2)} : Set ℂ)ᶜ) ↔ u ≠ 0 ∧ u ≠ -(1 / 2) := fun {u} => by
    simp [not_or]
  have h₁ : DifferentiableOn ℂ resA₁ (({0, -(1 / 2)} : Set ℂ)ᶜ) := fun u hu => by
    obtain ⟨h0, hm⟩ := hmem.1 hu
    have hd : (1 + 2 * u) * (2 * u) ≠ 0 :=
      mul_ne_zero (fun h => hm (by linear_combination h / 2)) (mul_ne_zero two_ne_zero h0)
    unfold resA₁
    exact (((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v - 1 / 2) u).mul
      (differentiable_xi_shift u)).div (by fun_prop) hd).differentiableWithinAt
  have h₂ : DifferentiableOn ℂ resA₂ (({0, -(1 / 2)} : Set ℂ)ᶜ) := fun u hu => by
    obtain ⟨h0, -⟩ := hmem.1 hu
    unfold resA₂
    exact (((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) u).div
      (by fun_prop) (mul_ne_zero (by norm_num) h0)).differentiableWithinAt
  have h₃ : DifferentiableOn ℂ resA₃ (({0, -(1 / 2)} : Set ℂ)ᶜ) := by unfold resA₃; fun_prop
  have hI := differentiableOn_integral_shape hg hρ0 hρ hV h₁ h₂ h₃
  have hc := hI.comp (f := fun s : ℂ => s - 1 / 2) (s := ({0, 1 / 2} : Set ℂ)ᶜ) (by fun_prop)
    fun s hs => by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs ⊢
      exact ⟨fun h => hs.2 (by linear_combination h), fun h => hs.1 (by linear_combination h)⟩
  exact hc

theorem residueRS_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    residueRS g s = (s - 1) * completedRS g s := by
  unfold residueRS completedRS
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [shape_res_eq (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination h))
    (fun h => h0 (by linear_combination h)), show s - 1 / 2 - 1 / 2 = s - 1 by ring]
  ring

theorem residueRS_one :
    residueRS g 1 = (1 / 4 : ℂ) * ((∫ z in ModularGroup.fd, ‖g z‖ ^ 2 : ℝ) : ℂ) := by
  unfold residueRS
  rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
  simp_rw [shape_res_half]
  rw [integral_mul_const, integral_complex_ofReal]
  ring

/-! ### The Gamma–zeta factor at `s = 1` -/

theorem xi_two_eq : xi (2 * 1) = (Real.pi : ℂ) / 6 := by
  have hpi0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [mul_one, xi_two]
  have hG : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    rw [Gammaℝ_def]; norm_num [Complex.Gamma_one, cpow_neg_one]
  have h := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  rw [riemannZeta_two, hG, div_inv_eq_mul] at h
  exact mul_right_cancel₀ hpi0 (h.symm.trans (by ring))

/-- `c(1) = π²/(96 cosh πt)`, `t = √(λ - ¼)`. -/
theorem rsFactor_one :
    rsFactor lamE 1 = ((Real.pi ^ 2 / (96 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4))) : ℝ) : ℂ) := by
  set t := Real.sqrt (lamE - 1 / 4)
  have hpi0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hch : (Real.cosh (Real.pi * t) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.cosh_pos _).ne'
  have hν : nu lamE = (t : ℂ) * I := rfl
  have hrefl : Gamma ((1 + nu lamE + nu lamE) / 2) * Gamma ((1 - nu lamE - nu lamE) / 2) =
      (Real.pi : ℂ) / (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (1 - nu lamE - nu lamE) / 2 = 1 - (1 + nu lamE + nu lamE) / 2 by ring,
      Gamma_mul_Gamma_one_sub,
      show (Real.pi : ℂ) * ((1 + nu lamE + nu lamE) / 2) = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi / 2 by
        rw [hν]; push_cast; ring, sin_add_pi_div_two, cos_mul_I, ← ofReal_cosh]
  have hhalf : Gamma (1 / 2) * Gamma (1 / 2) = (Real.pi : ℂ) := by
    rw [Gamma_one_half_eq, ← cpow_add _ _ hpi0]; norm_num
  have h2 : (2 : ℂ) ^ ((1 : ℂ) - 3) = 1 / 4 := by
    rw [show (1 : ℂ) - 3 = -((2 : ℕ) : ℂ) by norm_num, cpow_neg, cpow_natCast]; norm_num
  unfold rsFactor CuspRSI.gammaFactor
  rw [xi_two_eq, h2, cpow_neg_one, Gamma_one,
    show (1 + nu lamE - nu lamE) / 2 = (1 / 2 : ℂ) by ring,
    show (1 - nu lamE + nu lamE) / 2 = (1 / 2 : ℂ) by ring,
    show Gamma ((1 + nu lamE + nu lamE) / 2) * Gamma (1 / 2) * Gamma (1 / 2) *
        Gamma ((1 - nu lamE - nu lamE) / 2) = (Gamma ((1 + nu lamE + nu lamE) / 2) *
          Gamma ((1 - nu lamE - nu lamE) / 2)) * (Gamma (1 / 2) * Gamma (1 / 2)) by ring,
    hrefl, hhalf]
  push_cast
  field_simp
  ring

/-! ### The normalized Rankin–Selberg function -/

/-- `φ_g = F_g/c`: `(s - 1)` times the Rankin–Selberg series. -/
def rsPhi (lamE : ℝ) (g : UpperHalfPlane → ℂ) (s : ℂ) : ℂ := residueRS g s / rsFactor lamE s

theorem differentiableAt_rsPhi (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (rsPhi lamE g) s := by
  have hmem : s ∈ ({0, 1 / 2} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h] at hs; simp at hs; linarith
    · rw [h] at hs; norm_num at hs
  have hopen : IsOpen (({0, 1 / 2} : Set ℂ)ᶜ) := (Set.toFinite _).isClosed.isOpen_compl
  exact ((differentiableOn_residueRS hg hρ0 hρ).differentiableAt (hopen.mem_nhds hmem)).div
    (differentiableAt_rsFactor hs) (rsFactor_ne_zero hs)

/-- The mean-square constant `(24/π²) cosh(π√(λ-¼)) ‖g‖²`. -/
def msConst (lamE : ℝ) (g : UpperHalfPlane → ℂ) : ℝ :=
  24 / Real.pi ^ 2 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4)) * ∫ z in ModularGroup.fd, ‖g z‖ ^ 2

theorem rsPhi_one : rsPhi lamE g 1 = (msConst lamE g : ℂ) := by
  unfold rsPhi msConst
  rw [residueRS_one, rsFactor_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hch : Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4)) ≠ 0 := (Real.cosh_pos _).ne'
  push_cast
  field_simp
  ring

/-! ### The Dirichlet series over `ℕ` -/

/-- `f(m) = |ρ(m)|² + |ρ(-m)|²`. -/
def rsCoeff (ρ : ℤ → ℂ) (m : ℕ) : ℝ := ‖ρ m‖ ^ 2 + ‖ρ (-(m : ℤ))‖ ^ 2

theorem summable_sq_all (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℤ => ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-σ) := by
  obtain ⟨A, -, hA⟩ := CuspRS.summable_sq hg hρ0 hρ
  set σ' := min σ 2
  have h1 : 1 < σ' := lt_min hσ (by norm_num)
  refine (hA σ' h1 (min_le_right _ _)).1.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  by_cases hn : n = 0
  · simp [hn, hρ0]
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1
    (by simp only [σ', neg_le_neg_iff]; exact min_le_left _ _)) (sq_nonneg _)

theorem summable_nterm (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) σ) := by
  refine (summable_sq_all hg hρ0 hρ hσ).hasSum.nat_add_neg.summable.congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [nterm, hρ0]
  · simp only [nterm, hn, if_false, rsCoeff, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg (Nat.cast_nonneg _),
      div_eq_mul_inv]
    ring

theorem lSeriesSummable (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {y : ℝ} (hy : 1 < y) :
    LSeriesSummable (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) y := by
  refine Summable.of_norm ((summable_nterm hg hρ0 hρ hy).congr fun n => ?_)
  simp only [nterm, LSeries.norm_term_eq, ofReal_re]

theorem tsum_eq_LSeries (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) =
      LSeries (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) s := by
  have hsum : Summable fun n : ℤ => ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded (summable_sq_all hg hρ0 hρ hs) fun n => ?_
    by_cases hn : n = 0
    · simp [hn, hρ0]
    · have hpos : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
        norm_cpow_eq_rpow_re_of_pos hpos, neg_re]
  have h := hsum.hasSum.nat_add_neg
  have hH0 : ((‖ρ 0‖ ^ 2 : ℝ) : ℂ) * ((|((0 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) = 0 := by simp [hρ0]
  rw [hH0, add_zero] at h
  rw [← h.tsum_eq, LSeries]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp [hρ0]
  · rw [LSeries.term_of_ne_zero hn, rsCoeff]
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
    rw [show ((n : ℝ) : ℂ) = (n : ℂ) by push_cast; rfl, cpow_neg]
    push_cast
    ring

/-- **On `Re s > 1`, `φ_g(s)/(s - 1)` is the Rankin–Selberg Dirichlet series.** -/
theorem rsPhi_div_eq_LSeries (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    rsPhi lamE g s / (s - 1) = LSeries (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) s := by
  set T : Set ℂ := {s | 1 < s.re}
  set S : Set ℂ := {s | 1 < s.re ∧ s.im ≠ 0}
  have hne1 : ∀ s ∈ T, s ≠ 1 := fun s hs h => by rw [h] at hs; simp [T] at hs
  have hEq : EqOn (fun s => rsPhi lamE g s / (s - 1)) (LSeries fun n => ((rsCoeff ρ n : ℝ) : ℂ)) S := by
    rintro s ⟨hs, him⟩
    have h0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
    have h1 : s ≠ 1 / 2 := fun h => by rw [h] at hs; norm_num at hs
    have h2 : s ≠ 1 := hne1 s hs
    have hc := (rankinSelberg_continuation hg hρ0 hρ).2 s hs him
    show rsPhi lamE g s / (s - 1) = _
    rw [← tsum_eq_LSeries hg hρ0 hρ hs, ← hc, rsPhi, residueRS_eq h0 h1 h2, mul_div_assoc,
      mul_div_cancel_left₀ _ (sub_ne_zero.2 h2)]
  have hcL : ContinuousOn (fun s => rsPhi lamE g s / (s - 1)) T := fun s hs =>
    ((differentiableAt_rsPhi hg hρ0 hρ (by simp only [T, mem_setOf_eq] at hs; linarith)).continuousAt.div
      (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 (hne1 s hs))).continuousWithinAt
  have hcR : ContinuousOn (LSeries fun n => ((rsCoeff ρ n : ℝ) : ℂ)) T := by
    have hab : LSeries.abscissaOfAbsConv (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) ≤ ((1 : ℝ) : EReal) :=
      LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        lSeriesSummable hg hρ0 hρ hy
    refine (LSeries_differentiableOn _).continuousOn.mono fun s hs => ?_
    exact lt_of_le_of_lt hab (EReal.coe_lt_coe_iff.2 hs)
  have hcl : T ⊆ closure S := by
    intro s hs
    by_cases him : s.im = 0
    · have ht : Tendsto (fun t : ℝ => s + (t : ℂ) * I) (𝓝[>] 0) (𝓝 s) := by
        have : Continuous fun t : ℝ => s + (t : ℂ) * I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun t (htp : 0 < t) => ?_)
      refine ⟨by simpa [T] using hs, ?_⟩
      simp [him, htp.ne']
    · exact subset_closure ⟨hs, him⟩
  exact hEq.of_subset_closure hcL hcR (fun s hs => hs.1) hcl hs

/-! ### The mean-square law -/

/-- **The Rankin–Selberg mean-square law.** For a cusp form `g` of eigenvalue `λ` with Whittaker
coefficients `ρ(n)`, `(1/N) Σ_{|n|<N} |ρ(n)|² → (24/π²) cosh(π√(λ-¼)) ∫_𝒟 |g|² dμ`. -/
theorem tendsto_mean_square (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N, (‖ρ m‖ ^ 2 + ‖ρ (-(m : ℤ))‖ ^ 2)) / N) atTop
      (𝓝 (24 / Real.pi ^ 2 * Real.cosh (Real.pi * Real.sqrt (lamE - 1 / 4)) *
        ∫ z in ModularGroup.fd, ‖g z‖ ^ 2)) := by
  have hS : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hφ : DifferentiableOn ℂ (rsPhi lamE g) {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    (differentiableAt_rsPhi hg hρ0 hρ hs).differentiableWithinAt
  have hcont : ContinuousOn (dslope (rsPhi lamE g) 1) {s : ℂ | 1 ≤ s.re} :=
    ((continuousOn_dslope hS).2 ⟨hφ.continuousOn, differentiableAt_rsPhi hg hρ0 hρ (by norm_num)⟩).mono
      fun s hs => by simp only [mem_setOf_eq] at hs ⊢; linarith
  have heq : EqOn (dslope (rsPhi lamE g) 1) (fun s => LSeries (fun n => ((rsCoeff ρ n : ℝ) : ℂ)) s -
      ((msConst lamE g : ℝ) : ℂ) / (s - 1)) {s | 1 < s.re} := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
    dsimp only
    rw [dslope_of_ne _ hs1, slope_def_field, ← rsPhi_div_eq_LSeries hg hρ0 hρ hs, rsPhi_one, sub_div]
  have hWI := WienerIkeharaTheorem'' (f := rsCoeff ρ) (A := msConst lamE g)
    (G := dslope (rsPhi lamE g) 1) (fun n => by simp only [Pi.zero_apply, rsCoeff]; positivity)
    (fun σ hσ => summable_nterm hg hρ0 hρ hσ) hcont heq
  exact hWI

end CuspMS

end GaloisForLFunctions.BlackHoleRingdown
