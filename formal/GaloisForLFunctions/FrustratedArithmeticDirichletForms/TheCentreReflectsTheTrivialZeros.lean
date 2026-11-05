import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheWindowEnergyHasNoTrace
import GaloisForLFunctions.SignedWindowCriticality.TheParitySectorsAreTheBandAtTheCentre

/-!
# The centre reflects the trivial zeros

The parity sectors of the window `[−c, c]` are forms on the half-window `[−c, 0]` (SWC): with
`m_j(f) = ∫ f(u)e^{α_j u}du`, `α_j = 2j + ½`, the odd sector is `4S² ≤ M + Σ_j m_j² + P` and the even
sector `Σ_j m_j² + P ≤ M + 4C²`, where `M = W − 2C² + 2S²` and `P = Σ_n w_n(f⋆f)(−log n)`. The squares
`m_j²` are the archimedean coupling of a half-window test with its mirror: the trivial zeros. This
module shows that the half-window pays them exactly, mode by mode, through jumps across the centre:
the centre of a symmetric window is a boundary of the half-window, reflecting in the even sector and
anti-reflecting in the odd sector.

* **Mode identity** (`sq_moment_add_neumann_eq`, `dirichlet_eq_add_sq_moment`). For every `α` and
  `f` vanishing off `[−c, 0]`, with `K_α(f) = (∫_{−c}^0 e^{αv}dv)·∫ f²e^{αu}` (the mirror-hit mass of
  mode `α`):
  `m_α(f)² + ½∬ e^{α(u+v)}(f(u) − f(v))² = K_α(f)` and `½∬ e^{α(u+v)}(f(u) + f(v))² = K_α(f) + m_α(f)²`.
  Each trivial-zero square is its mode's mirror mass minus a reflected (Neumann) energy; added, it is
  an antireflected (Dirichlet) energy minus the mirror mass.
* **The mirror mass is centre killing** (`mirrorKilling_sum_le_edgeKilling`). For `α_j = 2j + ½`,
  `Σ_{j<N} K_{α_j}(f) ≤ 𝒦(f)`, the killing energy of the centre edge of the half-window, since
  `Σ_j e^{−α_j x} = ω(x)` and `∫_0^∞ e^{−αx}m_0(x)dx = α^{−1}∫f²e^{αu}`.
* **Sector forms** (`even_sector_iff_reflected`, `odd_sector_iff_antireflected`). The even sector
  holds iff `P ≤ (M − Σ_jK_j) + Σ_j N_j + 4C²` and the odd sector iff
  `4S² ≤ (M − Σ_jK_j) + Σ_j D_j + P`, with `N_j, D_j ≥ 0` the reflected and antireflected energies.

Since `M − Σ_jK_j = 2θ′(0)‖f‖² + (regional energy) + (outer-edge killing) + (centre killing − Σ_jK_j)`
and every bracket is nonnegative (`levyEnergy_sub_mirrorKilling_ge`), the trivial zeros are not part
of the frustration of either sector: what remains to be paid is the constant potential, the pole
square (odd) and the prime reflections (both).
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower (leftMoment trivialExponent)

variable {f : ℝ → ℝ} {c α : ℝ}

/-- The mirror moment `m_α(f) = ∫ f(u)e^{αu}du`. -/
def mirrorMoment (f : ℝ → ℝ) (α : ℝ) : ℝ := ∫ u, f u * Real.exp (α * u)

/-- The mirror-hit mass of mode `α`: `K_α(f) = (∫_{−c}^0 e^{αv}dv)·∫ f²e^{αu}`. -/
def mirrorKilling (c : ℝ) (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  (∫ v in Icc (-c) 0, Real.exp (α * v)) * ∫ u, f u ^ 2 * Real.exp (α * u)

/-- The reflected (Neumann) energy of mode `α` on `[−c, 0]`. -/
def neumannEnergy (c : ℝ) (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / 2) * ∫ u in Icc (-c) 0, ∫ v in Icc (-c) 0, Real.exp (α * (u + v)) * (f u - f v) ^ 2

/-- The antireflected (Dirichlet) energy of mode `α` on `[−c, 0]`. -/
def dirichletEnergy (c : ℝ) (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / 2) * ∫ u in Icc (-c) 0, ∫ v in Icc (-c) 0, Real.exp (α * (u + v)) * (f u + f v) ^ 2

theorem neumannEnergy_nonneg (c : ℝ) (f : ℝ → ℝ) (α : ℝ) : 0 ≤ neumannEnergy c f α :=
  mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Icc fun _ _ =>
    setIntegral_nonneg measurableSet_Icc fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

theorem dirichletEnergy_nonneg (c : ℝ) (f : ℝ → ℝ) (α : ℝ) : 0 ≤ dirichletEnergy c f α :=
  mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Icc fun _ _ =>
    setIntegral_nonneg measurableSet_Icc fun _ _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

/-- A function vanishing off `[−c, 0]` integrates over `[−c, 0]`. -/
theorem integral_eq_setIntegral_of_vanish {g : ℝ → ℝ} (hg : ∀ u, u ∉ Icc (-c) 0 → g u = 0) :
    ∫ u, g u = ∫ u in Icc (-c) 0, g u := by
  rw [← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Icc (-c) 0
  · rw [indicator_of_mem hu]
  · rw [indicator_of_notMem hu, hg u hu]

/-- The three moments of mode `α` as set integrals. -/
theorem mode_inner (hfc : Continuous f) (u : ℝ) :
    ∫ v in Icc (-c) 0, Real.exp (α * (u + v)) * (f u - f v) ^ 2 =
      Real.exp (α * u) * f u ^ 2 * (∫ v in Icc (-c) 0, Real.exp (α * v)) -
        2 * (Real.exp (α * u) * f u) * (∫ v in Icc (-c) 0, f v * Real.exp (α * v)) +
          Real.exp (α * u) * ∫ v in Icc (-c) 0, f v ^ 2 * Real.exp (α * v) := by
  have i1 : IntegrableOn (fun v => Real.exp (α * v)) (Icc (-c) 0) :=
    (by fun_prop : Continuous fun v => Real.exp (α * v)).integrableOn_Icc
  have i2 : IntegrableOn (fun v => f v * Real.exp (α * v)) (Icc (-c) 0) :=
    (hfc.mul (by fun_prop)).integrableOn_Icc
  have i3 : IntegrableOn (fun v => f v ^ 2 * Real.exp (α * v)) (Icc (-c) 0) :=
    ((hfc.pow 2).mul (by fun_prop)).integrableOn_Icc
  have hpt : ∀ v, Real.exp (α * (u + v)) * (f u - f v) ^ 2 =
      Real.exp (α * u) * f u ^ 2 * Real.exp (α * v) -
        2 * (Real.exp (α * u) * f u) * (f v * Real.exp (α * v)) +
          Real.exp (α * u) * (f v ^ 2 * Real.exp (α * v)) := by
    intro v
    rw [show α * (u + v) = α * u + α * v by ring, Real.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_sub_add_three (i1.const_mul _) (i2.const_mul _) (i3.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]

theorem mode_inner_plus (hfc : Continuous f) (u : ℝ) :
    ∫ v in Icc (-c) 0, Real.exp (α * (u + v)) * (f u + f v) ^ 2 =
      Real.exp (α * u) * f u ^ 2 * (∫ v in Icc (-c) 0, Real.exp (α * v)) +
        2 * (Real.exp (α * u) * f u) * (∫ v in Icc (-c) 0, f v * Real.exp (α * v)) +
          Real.exp (α * u) * ∫ v in Icc (-c) 0, f v ^ 2 * Real.exp (α * v) := by
  have i1 : IntegrableOn (fun v => Real.exp (α * v)) (Icc (-c) 0) :=
    (by fun_prop : Continuous fun v => Real.exp (α * v)).integrableOn_Icc
  have i2 : IntegrableOn (fun v => f v * Real.exp (α * v)) (Icc (-c) 0) :=
    (hfc.mul (by fun_prop)).integrableOn_Icc
  have i3 : IntegrableOn (fun v => f v ^ 2 * Real.exp (α * v)) (Icc (-c) 0) :=
    ((hfc.pow 2).mul (by fun_prop)).integrableOn_Icc
  have hpt : ∀ v, Real.exp (α * (u + v)) * (f u + f v) ^ 2 =
      Real.exp (α * u) * f u ^ 2 * Real.exp (α * v) +
        2 * (Real.exp (α * u) * f u) * (f v * Real.exp (α * v)) +
          Real.exp (α * u) * (f v ^ 2 * Real.exp (α * v)) := by
    intro v
    rw [show α * (u + v) = α * u + α * v by ring, Real.exp_add]
    ring
  simp_rw [hpt]
  rw [integral_add_three (i1.const_mul _) (i2.const_mul _) (i3.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]

/-- Outer integration of the mode expansion: `A·B − 2m·m + A·B` with `A = ∫e^{αv}`,
`B = ∫f²e^{αu}`, `m = ∫fe^{αu}`, all over `[−c, 0]`. -/
theorem mode_outer (hfc : Continuous f) (s : ℝ) :
    ∫ u in Icc (-c) 0, (Real.exp (α * u) * f u ^ 2 * (∫ v in Icc (-c) 0, Real.exp (α * v)) +
        s * (Real.exp (α * u) * f u) * (∫ v in Icc (-c) 0, f v * Real.exp (α * v)) +
          Real.exp (α * u) * ∫ v in Icc (-c) 0, f v ^ 2 * Real.exp (α * v)) =
      2 * ((∫ v in Icc (-c) 0, Real.exp (α * v)) * ∫ u in Icc (-c) 0, f u ^ 2 * Real.exp (α * u)) +
        s * (∫ u in Icc (-c) 0, f u * Real.exp (α * u)) ^ 2 := by
  set A := ∫ v in Icc (-c) 0, Real.exp (α * v)
  set m := ∫ v in Icc (-c) 0, f v * Real.exp (α * v)
  set B := ∫ v in Icc (-c) 0, f v ^ 2 * Real.exp (α * v)
  have i1 : IntegrableOn (fun u => Real.exp (α * u) * f u ^ 2 * A) (Icc (-c) 0) :=
    (((by fun_prop : Continuous fun u => Real.exp (α * u)).mul (hfc.pow 2)).mul
      continuous_const).integrableOn_Icc
  have i2 : IntegrableOn (fun u => s * (Real.exp (α * u) * f u) * m) (Icc (-c) 0) :=
    ((continuous_const.mul ((by fun_prop : Continuous fun u => Real.exp (α * u)).mul hfc)).mul
      continuous_const).integrableOn_Icc
  have i3 : IntegrableOn (fun u => Real.exp (α * u) * B) (Icc (-c) 0) :=
    ((by fun_prop : Continuous fun u => Real.exp (α * u)).mul continuous_const).integrableOn_Icc
  rw [integral_add_three i1 i2 i3, integral_mul_const, integral_mul_const,
    integral_mul_const, integral_const_mul]
  have e1 : ∫ u in Icc (-c) 0, Real.exp (α * u) * f u ^ 2 = B :=
    setIntegral_congr_fun measurableSet_Icc fun u _ => by ring
  have e2 : ∫ u in Icc (-c) 0, Real.exp (α * u) * f u = m :=
    setIntegral_congr_fun measurableSet_Icc fun u _ => by ring
  rw [e1, e2]
  ring

/-- **Mode identity, reflected.** `m_α(f)² + N_α(f) = K_α(f)` for `f` vanishing off `[−c, 0]`. -/
theorem sq_moment_add_neumann_eq (hfc : Continuous f) (hf : ∀ u, u ∉ Icc (-c) 0 → f u = 0) (α : ℝ) :
    mirrorMoment f α ^ 2 + neumannEnergy c f α = mirrorKilling c f α := by
  have hm : mirrorMoment f α = ∫ u in Icc (-c) 0, f u * Real.exp (α * u) :=
    integral_eq_setIntegral_of_vanish fun u hu => by rw [hf u hu, zero_mul]
  have hB : (∫ u, f u ^ 2 * Real.exp (α * u)) = ∫ u in Icc (-c) 0, f u ^ 2 * Real.exp (α * u) :=
    integral_eq_setIntegral_of_vanish fun u hu => by rw [hf u hu]; ring
  have hN : neumannEnergy c f α = (1 / 2) *
      (2 * ((∫ v in Icc (-c) 0, Real.exp (α * v)) * ∫ u in Icc (-c) 0, f u ^ 2 * Real.exp (α * u)) +
        -2 * (∫ u in Icc (-c) 0, f u * Real.exp (α * u)) ^ 2) := by
    unfold neumannEnergy
    rw [← mode_outer hfc (-2)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    rw [mode_inner hfc u]
    ring
  rw [hN, hm]
  unfold mirrorKilling
  rw [hB]
  ring

/-- **Mode identity, antireflected.** `D_α(f) = K_α(f) + m_α(f)²`. -/
theorem dirichlet_eq_add_sq_moment (hfc : Continuous f) (hf : ∀ u, u ∉ Icc (-c) 0 → f u = 0)
    (α : ℝ) : dirichletEnergy c f α = mirrorKilling c f α + mirrorMoment f α ^ 2 := by
  have hm : mirrorMoment f α = ∫ u in Icc (-c) 0, f u * Real.exp (α * u) :=
    integral_eq_setIntegral_of_vanish fun u hu => by rw [hf u hu, zero_mul]
  have hB : (∫ u, f u ^ 2 * Real.exp (α * u)) = ∫ u in Icc (-c) 0, f u ^ 2 * Real.exp (α * u) :=
    integral_eq_setIntegral_of_vanish fun u hu => by rw [hf u hu]; ring
  have hD : dirichletEnergy c f α = (1 / 2) *
      (2 * ((∫ v in Icc (-c) 0, Real.exp (α * v)) * ∫ u in Icc (-c) 0, f u ^ 2 * Real.exp (α * u)) +
        2 * (∫ u in Icc (-c) 0, f u * Real.exp (α * u)) ^ 2) := by
    unfold dirichletEnergy
    rw [← mode_outer hfc 2]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    rw [mode_inner_plus hfc u]
  rw [hD, hm]
  unfold mirrorKilling
  rw [hB]
  ring

/-! ### The mirror mass is killing at the centre -/

theorem setIntegral_exp_Icc_le {α : ℝ} (hα : 0 < α) (c : ℝ) :
    ∫ v in Icc (-c) 0, Real.exp (α * v) ≤ 1 / α := by
  have h := integral_exp_mul_Iic hα 0
  rw [mul_zero, Real.exp_zero] at h
  rw [← h]
  exact setIntegral_mono_set (integrableOn_exp_mul_Iic hα 0)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (Eventually.of_forall fun v (hv : v ∈ Icc (-c) 0) => (show v ∈ Iic (0 : ℝ) from hv.2))

theorem integrable_sq_mul_exp (hfc : Continuous f) (hfs : HasCompactSupport f) (α : ℝ) :
    Integrable fun u => f u ^ 2 * Real.exp (α * u) := by
  have hsub : Function.support (fun u => f u ^ 2 * Real.exp (α * u)) ⊆ Function.support f :=
    fun u hu => Function.mem_support.mpr fun h => Function.mem_support.mp hu (by simp [h])
  exact ((hfc.pow 2).mul (by fun_prop)).integrable_of_hasCompactSupport
    (hfs.mono hsub)

/-- The mirror mass is at most the full centre mass `α^{−1}∫f²e^{αu}`. -/
theorem mirrorKilling_le (hfc : Continuous f) (hfs : HasCompactSupport f) {α : ℝ} (hα : 0 < α) :
    mirrorKilling c f α ≤ (1 / α) * ∫ u, f u ^ 2 * Real.exp (α * u) :=
  mul_le_mul_of_nonneg_right (setIntegral_exp_Icc_le hα c)
    (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

theorem mirrorKilling_nonneg (c : ℝ) (f : ℝ → ℝ) (α : ℝ) : 0 ≤ mirrorKilling c f α :=
  mul_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => (Real.exp_pos _).le)
    (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

/-- **Fubini at the centre edge**: `∫_0^∞ e^{−αx}m_0(x)dx = α^{−1}∫ f²e^{αu}` for `f` vanishing on
`(0, ∞)`, where `m_0(x)` is the mass of `f²` within `x` of the edge `0`. -/
theorem integral_exp_mul_rightEdgeMass (hfc : Continuous f) (hfs : HasCompactSupport f)
    (h0 : ∀ u, 0 < u → f u = 0) {α : ℝ} (hα : 0 < α) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-α * x) * rightEdgeMass f 0 x =
      (1 / α) * ∫ u, f u ^ 2 * Real.exp (α * u) := by
  have hsq := integrable_sq_of_cont hfc hfs
  set G : ℝ → ℝ → ℝ := fun x u => Real.exp (-α * x) * (Ioi (-x)).indicator (fun u => f u ^ 2) u
  have hGint : Integrable (Function.uncurry G) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-α * p.1) * f p.2 ^ 2)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
      Integrable.mul_prod (exp_neg_integrableOn_Ioi 0 hα) hsq
    have hGm : Measurable (Function.uncurry G) := by
      have e : Function.uncurry G = fun p : ℝ × ℝ => Real.exp (-α * p.1) *
          ({q : ℝ × ℝ | -q.1 < q.2}.indicator (fun q => f q.2 ^ 2) p) := by
        funext p
        simp only [Function.uncurry, G, Set.indicator_apply, mem_Ioi, mem_setOf_eq]
      rw [e]
      exact (by fun_prop : Measurable fun p : ℝ × ℝ => Real.exp (-α * p.1)).mul
        (((hfc.pow 2).measurable.comp measurable_snd).indicator
          (measurableSet_lt measurable_fst.neg measurable_snd))
    refine hdom.mono' hGm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, G, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    by_cases h : p.2 ∈ Ioi (-p.1)
    · rw [indicator_of_mem h, abs_of_nonneg (sq_nonneg _)]
    · rw [indicator_of_notMem h, abs_zero]; exact sq_nonneg _
  have hswap := integral_integral_swap hGint
  have hlhs : ∫ x in Ioi (0 : ℝ), Real.exp (-α * x) * rightEdgeMass f 0 x =
      ∫ x in Ioi (0 : ℝ), ∫ u, G x u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [G, rightEdgeMass, zero_sub]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  have hinner : ∀ u, ∫ x in Ioi (0 : ℝ), G x u = (1 / α) * (f u ^ 2 * Real.exp (α * u)) := by
    intro u
    by_cases hu : 0 < u
    · have hz : ∀ x, G x u = 0 := fun x => by
        simp only [G]
        by_cases h : u ∈ Ioi (-x)
        · rw [indicator_of_mem h, h0 u hu]; ring
        · rw [indicator_of_notMem h, mul_zero]
      simp_rw [hz, integral_zero, h0 u hu]
      ring
    · push_neg at hu
      have hpt : EqOn (fun x => G x u)
          (fun x => (Ioi (-u)).indicator (fun x => f u ^ 2 * Real.exp (-α * x)) x) (Ioi 0) := by
        intro x _
        simp only [G]
        by_cases h : u ∈ Ioi (-x)
        · have h' : x ∈ Ioi (-u) := by simp only [mem_Ioi] at h ⊢; linarith
          rw [indicator_of_mem h, indicator_of_mem h']; ring
        · have h' : x ∉ Ioi (-u) := by simp only [mem_Ioi, not_lt] at h ⊢; linarith
          rw [indicator_of_notMem h, indicator_of_notMem h', mul_zero]
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi (by linarith)), integral_const_mul,
        integral_exp_mul_Ioi (by linarith) (-u)]
      rw [show -α * -u = α * u by ring]
      have hα0 := hα.ne'
      field_simp
  rw [hlhs, hswap]
  simp_rw [hinner]
  rw [integral_const_mul]

/-- The trivial-zero exponents `α_j = 2j + ½`. -/
def trivialMode (j : ℕ) : ℝ := 2 * j + 1 / 2

theorem trivialMode_pos (j : ℕ) : 0 < trivialMode j := by unfold trivialMode; positivity

/-- **The mirror masses of all trivial-zero modes are paid by the centre-edge killing.**
`Σ_{j<N} K_{α_j}(f) ≤ ∫_0^∞ ω(x)m_0(x)dx` for every `N`. -/
theorem sum_mirrorKilling_le (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) (N : ℕ) :
    ∑ j ∈ Finset.range N, mirrorKilling c f (trivialMode j) ≤
      ∫ x in Ioi (0 : ℝ), archLevyDensity x * rightEdgeMass f 0 x := by
  have hfc := hf.continuous
  have h0 : ∀ u, 0 < u → f u = 0 := fun u hu => hab u fun h => by linarith [h.2]
  have hmono := monotone_rightEdgeMass hfc hfs 0
  have hmeas : Measurable (rightEdgeMass f 0) := hmono.measurable
  have hbound : ∀ x, rightEdgeMass f 0 x ≤ ∫ u, f u ^ 2 := fun x =>
    setIntegral_le_integral (integrable_sq_of_cont hfc hfs) (Eventually.of_forall fun _ => sq_nonneg _)
  have hint : ∀ j, IntegrableOn (fun x => Real.exp (-trivialMode j * x) * rightEdgeMass f 0 x) (Ioi 0) := by
    intro j
    refine ((exp_neg_integrableOn_Ioi 0 (trivialMode_pos j)).mul_const (∫ u, f u ^ 2)).mono'
      ((((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul
        hmeas).aestronglyMeasurable) (ae_restrict_of_forall_mem measurableSet_Ioi fun x _ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (rightEdgeMass_nonneg f 0 x))]
    rw [show -trivialMode j * x = -(trivialMode j * x) by ring]
    exact mul_le_mul_of_nonneg_left (hbound x) (Real.exp_pos _).le
  calc ∑ j ∈ Finset.range N, mirrorKilling c f (trivialMode j)
      ≤ ∑ j ∈ Finset.range N, (1 / trivialMode j) * ∫ u, f u ^ 2 * Real.exp (trivialMode j * u) :=
        Finset.sum_le_sum fun j _ => mirrorKilling_le hfc hfs (trivialMode_pos j)
    _ = ∑ j ∈ Finset.range N, ∫ x in Ioi (0 : ℝ), Real.exp (-trivialMode j * x) * rightEdgeMass f 0 x :=
        Finset.sum_congr rfl fun j _ =>
          (integral_exp_mul_rightEdgeMass hfc hfs h0 (trivialMode_pos j)).symm
    _ = ∫ x in Ioi (0 : ℝ), (∑ j ∈ Finset.range N, Real.exp (-trivialMode j * x)) * rightEdgeMass f 0 x := by
        rw [← integral_finsetSum (Finset.range N) fun j _ => hint j]
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        simp only [Finset.sum_mul]
    _ ≤ ∫ x in Ioi (0 : ℝ), archLevyDensity x * rightEdgeMass f 0 x := by
        refine setIntegral_mono_on ?_ (integrableOn_rightEdge hf hfs hab) measurableSet_Ioi
          fun x hx => ?_
        · exact IntegrableOn.congr_fun (integrable_finsetSum (Finset.range N) fun j _ => hint j)
            (fun x _ => by simp only [Finset.sum_apply, Finset.sum_mul]) measurableSet_Ioi
        · refine mul_le_mul_of_nonneg_right ?_ (rightEdgeMass_nonneg f 0 x)
          have hx0 : (0 : ℝ) < x := hx
          rw [ArchimedeanAnomaly.archLevyDensity_eq_tsum hx0]
          have hr : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
          have hsum : Summable fun k : ℕ => Real.exp (-(2 * k + 1 / 2) * x) := by
            refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
              (Real.exp (-(1 / 2) * x))).congr fun k => ?_
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            ring
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => by
            simp only [trivialMode])) (hsum.sum_le_tsum _ (fun k _ => (Real.exp_pos _).le))

theorem summable_mirrorKilling (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) : Summable fun j => mirrorKilling c f (trivialMode j) :=
  summable_of_sum_range_le (fun _ => mirrorKilling_nonneg c f _) (sum_mirrorKilling_le hf hfs hab)

/-- **The summed mirror mass is at most the edge killing energy**, hence at most the window energy. -/
theorem tsum_mirrorKilling_le_edgeKilling (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    ∑' j, mirrorKilling c f (trivialMode j) ≤ edgeKilling f (-c) 0 :=
  (Real.tsum_le_of_sum_range_le (fun _ => mirrorKilling_nonneg c f _)
    (sum_mirrorKilling_le hf hfs hab)).trans (rightEdgeKilling_le_edgeKilling hf hfs hab)

/-- After the mirror is paid the window energy keeps its regional part:
`𝒥_reg(f) ≤ 𝒥(f) − Σ_jK_j(f)`. -/
theorem levyEnergy_sub_mirrorKilling_ge (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    regionalEnergy f (-c) 0 ≤ levyEnergy f - ∑' j, mirrorKilling c f (trivialMode j) := by
  rw [levyEnergy_eq_regional_add_edge hf hfs hab]
  linarith [tsum_mirrorKilling_le_edgeKilling hf hfs hab]

theorem summable_sq_mirrorMoment (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    Summable fun j => mirrorMoment f (trivialMode j) ^ 2 :=
  (summable_mirrorKilling hf hfs hab).of_nonneg_of_le (fun _ => sq_nonneg _) fun j => by
    have := sq_moment_add_neumann_eq hf.continuous hab (trivialMode j)
    linarith [neumannEnergy_nonneg c f (trivialMode j)]

theorem summable_neumannEnergy (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    Summable fun j => neumannEnergy c f (trivialMode j) :=
  (summable_mirrorKilling hf hfs hab).of_nonneg_of_le (fun _ => neumannEnergy_nonneg _ _ _)
    fun j => by
      have := sq_moment_add_neumann_eq hf.continuous hab (trivialMode j)
      linarith [sq_nonneg (mirrorMoment f (trivialMode j))]

theorem summable_dirichletEnergy (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    Summable fun j => dirichletEnergy c f (trivialMode j) :=
  ((summable_mirrorKilling hf hfs hab).add (summable_sq_mirrorMoment hf hfs hab)).congr fun j =>
    (dirichlet_eq_add_sq_moment hf.continuous hab (trivialMode j)).symm

/-- SWC's trivial-zero squares are the mirror moments of the modes `α_j`. -/
theorem trivialSquares_eq_tsum (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    leftMoment f (-(1 / 2)) ^ 2 + ∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2 =
      ∑' j, mirrorMoment f (trivialMode j) ^ 2 := by
  rw [(summable_sq_mirrorMoment hf hfs hab).tsum_eq_zero_add]
  have e0 : leftMoment f (-(1 / 2)) = mirrorMoment f (trivialMode 0) := by
    unfold leftMoment mirrorMoment trivialMode
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    try simp only
    congr 2
    push_cast
    ring
  have ek : ∀ k : ℕ, leftMoment f (trivialExponent k) = mirrorMoment f (trivialMode (k + 1)) := by
    intro k
    unfold leftMoment mirrorMoment trivialMode trivialExponent
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    try simp only
    congr 2
    push_cast
    ring
  rw [e0]
  simp_rw [ek]

/-- The trivial-zero squares are mirror mass minus reflected energy. -/
theorem trivialSquares_eq_mirror_sub_neumann (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    leftMoment f (-(1 / 2)) ^ 2 + ∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2 =
      ∑' j, mirrorKilling c f (trivialMode j) - ∑' j, neumannEnergy c f (trivialMode j) := by
  rw [trivialSquares_eq_tsum hf hfs hab, ← (summable_mirrorKilling hf hfs hab).tsum_sub
    (summable_neumannEnergy hf hfs hab)]
  exact tsum_congr fun j => by
    have := sq_moment_add_neumann_eq hf.continuous hab (trivialMode j)
    linarith

/-- The trivial-zero squares are antireflected energy minus mirror mass. -/
theorem trivialSquares_eq_dirichlet_sub_mirror (hf : ContDiff ℝ 2 f) (hfs : HasCompactSupport f)
    (hab : ∀ u, u ∉ Icc (-c) 0 → f u = 0) :
    leftMoment f (-(1 / 2)) ^ 2 + ∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2 =
      ∑' j, dirichletEnergy c f (trivialMode j) - ∑' j, mirrorKilling c f (trivialMode j) := by
  rw [trivialSquares_eq_tsum hf hfs hab, ← (summable_dirichletEnergy hf hfs hab).tsum_sub
    (summable_mirrorKilling hf hfs hab)]
  exact tsum_congr fun j => by
    have := dirichlet_eq_add_sq_moment hf.continuous hab (trivialMode j)
    linarith

theorem vanish_of_half {a : ℝ} (h0 : ∀ u, 0 < u → f u = 0) (ha : ∀ u, u < -a → f u = 0) :
    ∀ u, u ∉ Icc (-a) 0 → f u = 0 := fun u hu => by
  rcases not_and_or.mp hu with h | h
  · exact ha u (not_le.mp h)
  · exact h0 u (not_le.mp h)

/-- **The even sector reflects the trivial zeros.** The even sector of `[−a, a]` holds iff, on every
half-window test, the prime reflections are paid by the mirror-paid Markov energy, the reflected
energies of the trivial-zero modes and the pole square:
`P(f) ≤ (M(f) − Σ_jK_j(f)) + Σ_jN_j(f) + 4C(f)²`. -/
theorem even_sector_iff_reflected {a : ℝ} (ha : 0 < a) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) →
        SpacingScaleHarmonicAnalysis.SupportedIn a F → 0 ≤ SpacingScaleHarmonicAnalysis.weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -a → f u = 0) →
        (∑' n : ℕ, vonMangoldtAtom n * SignedWindowCriticality.selfConv f (2 * 0 - Real.log n)) ≤
          (SpacingScaleHarmonicAnalysis.weilQuad f - 2 * coshHalfMoment f ^ 2 +
              2 * sinhHalfMoment f ^ 2 - ∑' j, mirrorKilling a f (trivialMode j)) +
            ∑' j, neumannEnergy a f (trivialMode j) + 4 * coshHalfMoment f ^ 2 := by
  rw [SignedWindowCriticality.even_nonneg_iff_markov_hankel ha]
  refine forall_congr' fun f => imp_congr_right fun hf => imp_congr_right fun h0 =>
    imp_congr_right fun hfa => ?_
  have hab := vanish_of_half h0 hfa
  have hfs := SignedWindowCriticality.hasCompactSupport_of_half h0 hfa
  rw [trivialSquares_eq_mirror_sub_neumann hf hfs hab]
  constructor <;> intro h <;> linarith

/-- **The odd sector antireflects the trivial zeros.** The odd sector of `[−a, a]` holds iff
`4S(f)² ≤ (M(f) − Σ_jK_j(f)) + Σ_jD_j(f) + P(f)` on every half-window test. -/
theorem odd_sector_iff_antireflected {a : ℝ} (ha : 0 < a) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) →
        SpacingScaleHarmonicAnalysis.SupportedIn a F → 0 ≤ SpacingScaleHarmonicAnalysis.weilQuad F) ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -a → f u = 0) →
        4 * sinhHalfMoment f ^ 2 ≤
          (SpacingScaleHarmonicAnalysis.weilQuad f - 2 * coshHalfMoment f ^ 2 +
              2 * sinhHalfMoment f ^ 2 - ∑' j, mirrorKilling a f (trivialMode j)) +
            ∑' j, dirichletEnergy a f (trivialMode j) +
              ∑' n : ℕ, vonMangoldtAtom n * SignedWindowCriticality.selfConv f (2 * 0 - Real.log n) := by
  rw [SignedWindowCriticality.odd_nonneg_iff_markov_hankel ha]
  refine forall_congr' fun f => imp_congr_right fun hf => imp_congr_right fun h0 =>
    imp_congr_right fun hfa => ?_
  have hab := vanish_of_half h0 hfa
  have hfs := SignedWindowCriticality.hasCompactSupport_of_half h0 hfa
  have h := trivialSquares_eq_dirichlet_sub_mirror hf hfs hab
  have e : SpacingScaleHarmonicAnalysis.weilQuad f - 2 * coshHalfMoment f ^ 2 +
        2 * sinhHalfMoment f ^ 2 + leftMoment f (-(1 / 2)) ^ 2 +
        (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
        ∑' n : ℕ, vonMangoldtAtom n * SignedWindowCriticality.selfConv f (2 * 0 - Real.log n) =
      (SpacingScaleHarmonicAnalysis.weilQuad f - 2 * coshHalfMoment f ^ 2 +
          2 * sinhHalfMoment f ^ 2 - ∑' j, mirrorKilling a f (trivialMode j)) +
        ∑' j, dirichletEnergy a f (trivialMode j) +
          ∑' n : ℕ, vonMangoldtAtom n * SignedWindowCriticality.selfConv f (2 * 0 - Real.log n) := by
    rw [add_assoc (SpacingScaleHarmonicAnalysis.weilQuad f - 2 * coshHalfMoment f ^ 2 +
      2 * sinhHalfMoment f ^ 2) (leftMoment f (-(1 / 2)) ^ 2), h]
    ring
  rw [e]

/-- The mirror-paid Markov energy splits as the constant potential, minus the prime jumps inside the
half-window, plus the window energy left after the mirror, which dominates the regional energy. -/
theorem markov_sub_mirror_eq {a : ℝ} (hf : ContDiff ℝ 2 f) (h0 : ∀ u, 0 < u → f u = 0)
    (hfa : ∀ u, u < -a → f u = 0) :
    SpacingScaleHarmonicAnalysis.weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2 -
        ∑' j, mirrorKilling a f (trivialMode j) =
      2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) - primeSum f +
        (levyEnergy f - ∑' j, mirrorKilling a f (trivialMode j)) ∧
    regionalEnergy f (-a) 0 ≤ levyEnergy f - ∑' j, mirrorKilling a f (trivialMode j) := by
  have hfs := SignedWindowCriticality.hasCompactSupport_of_half h0 hfa
  refine ⟨?_, levyEnergy_sub_mirrorKilling_ge hf hfs (vanish_of_half h0 hfa)⟩
  rw [SpacingScaleHarmonicAnalysis.weilQuad_eq hf hfs]
  ring

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
