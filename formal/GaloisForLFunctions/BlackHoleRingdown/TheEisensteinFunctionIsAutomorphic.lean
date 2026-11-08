import GaloisForLFunctions.BlackHoleRingdown.TheRingdownExpansion

/-!
# The Eisenstein function is automorphic at every spectral parameter

The Eisenstein function `E(u; z)` of the modular horizon was known to be `SL₂(ℤ)`-invariant on the critical
line `u ∈ iℝ`. Its numerator `N(u; z) = ξ(1+2u) E(u; z)` is holomorphic on `u ≠ ½` (`differentiableAt_numerator`),
so the identity theorem carries the invariance to the whole plane (`numerator_smul`): **`E(u; ·)` is
automorphic at every regular point**, `u ≠ ½`, `ξ(1+2u) ≠ 0` (`normalizedEisenstein_smul_of_regular`).

The same argument gives the **functional equation**. Off the real axis the completed function
`E*(u; z) = N(u; z)/((1+2u)(2u))` is half the completed Fourier model
`Λ(2u)Y^{½-u} + Λ(1+2u)Y^{½+u} + 2T(u)`, which is even in `u` by `Λ(s) = Λ(1-s)`. Hence `E*(-u) = E*(u)` for
all `u ∉ {0, ±½}` (`completedEisenstein_neg`). These are Selberg's continuation and functional equation of
the Eisenstein series, recovered from the line.
-/

open Complex MeasureTheory Set Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

namespace EisAuto

/-- **The numerator is holomorphic away from `u = ½`.** -/
theorem differentiableAt_numerator (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : u ≠ 1 / 2) :
    DifferentiableAt ℂ (fun v => eisensteinNumerator v x Y) u := by
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 + v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 + v) u).const_cpow (Or.inl hYC)
  have h2 : DifferentiableAt ℂ (fun v : ℂ => (Y : ℂ) ^ (1 / 2 - v)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 / 2 - v) u).const_cpow (Or.inl hYC)
  have hx1 : DifferentiableAt ℂ (fun v : ℂ => xi (1 + 2 * v)) u := differentiable_xi_shift u
  have hx2 : DifferentiableAt ℂ (fun v : ℂ => xi (2 * v)) u :=
    (xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) u
  have hne : 2 * u - 1 ≠ 0 := fun h => hu (by linear_combination h / 2)
  have hq : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) / (2 * v - 1)) u :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 + 2 * v) u).div (by fun_prop) hne
  have hp : DifferentiableAt ℂ (fun v : ℂ => (1 + 2 * v) * (2 * v)) u := by fun_prop
  exact ((h1.mul hx1).add ((hq.mul hx2).mul h2)).add (hp.mul (differentiableAt_eisTail x hY u))

theorem preconnected_compl_finite {s : Set ℂ} (hs : s.Finite) : IsPreconnected sᶜ :=
  (hs.countable.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

/-- Points of the critical line accumulate at `i`. -/
theorem frequently_line {p : ℂ → Prop} (h : ∀ ξ : ℝ, ξ ≠ 0 → p ((ξ : ℂ) * I)) :
    ∃ᶠ v in 𝓝[≠] I, p v := by
  have ht : Tendsto (fun ξ : ℝ => (ξ : ℂ) * I) (𝓝[≠] (1 : ℝ)) (𝓝[≠] I) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun ξ : ℝ => (ξ : ℂ) * I) := by fun_prop
      have h1 := hc.tendsto 1
      simp only [ofReal_one, one_mul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ
      intro he
      apply hξ
      have := congrArg Complex.im he
      simpa using this
  refine ht.frequently ?_
  have hne : ∀ᶠ ξ in 𝓝[≠] (1 : ℝ), ξ ≠ 0 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((isOpen_ne (x := (0 : ℝ))).mem_nhds (one_ne_zero : (1 : ℝ) ≠ 0))
  exact (hne.mono fun ξ hξ => h ξ hξ).frequently

theorem I_ne_half : (I : ℂ) ≠ 1 / 2 := fun h => by
  have := congrArg Complex.im h
  simp at this

/-- **The numerator is automorphic at every `u ≠ ½`.** -/
theorem numerator_smul (γ : SL(2, ℤ)) (z : ℍ) {u : ℂ} (hu : u ≠ 1 / 2) :
    eisensteinNumerator u (γ • z).re (γ • z).im = eisensteinNumerator u z.re z.im := by
  have hU : IsOpen ({1 / 2}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : ∀ w : ℍ, DifferentiableOn ℂ (fun v => eisensteinNumerator v w.re w.im) {1 / 2}ᶜ :=
    fun w v hv => (differentiableAt_numerator w.re w.im_pos hv).differentiableWithinAt
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq ((hd _).analyticOnNhd hU)
    ((hd z).analyticOnNhd hU) (preconnected_compl_finite (Set.finite_singleton _))
    (show I ∈ ({1 / 2}ᶜ : Set ℂ) from I_ne_half) (frequently_line fun ξ hξ => ?_) hu
  have hx := xi_line_ne_zero ξ
  have hinv := normalizedEisenstein_smul hξ γ z
  rw [normalizedEisenstein_eq_numerator_div hx, normalizedEisenstein_eq_numerator_div hx] at hinv
  exact (div_left_inj' hx).1 hinv

/-- **The Eisenstein function is automorphic at every regular spectral parameter.** -/
theorem normalizedEisenstein_smul_of_regular (γ : SL(2, ℤ)) (z : ℍ) {u : ℂ} (hu : u ≠ 1 / 2)
    (hξ : xi (1 + 2 * u) ≠ 0) :
    normalizedEisenstein u (γ • z).re (γ • z).im = normalizedEisenstein u z.re z.im := by
  rw [normalizedEisenstein_eq_numerator_div hξ, normalizedEisenstein_eq_numerator_div hξ,
    numerator_smul γ z hu]

/-- The Eisenstein function is holomorphic at every regular spectral parameter. -/
theorem differentiableAt_normalizedEisenstein_of_regular (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ}
    (hu : u ≠ 1 / 2) (hξ : xi (1 + 2 * u) ≠ 0) :
    DifferentiableAt ℂ (fun v => normalizedEisenstein v x Y) u := by
  have hc : ContinuousAt (fun v : ℂ => xi (1 + 2 * v)) u := (differentiable_xi_shift u).continuousAt
  refine ((differentiableAt_numerator x hY hu).div (differentiable_xi_shift u) hξ).congr_of_eventuallyEq ?_
  filter_upwards [hc.eventually_ne hξ] with v hv
  exact normalizedEisenstein_eq_numerator_div hv x Y

/-! ### The functional equation -/

/-- The completed Eisenstein function `E*(u; x, Y) = ξ(1+2u) E(u; x, Y)/((1+2u)(2u))`. -/
def completedEisenstein (u : ℂ) (x Y : ℝ) : ℂ := eisensteinNumerator u x Y / ((1 + 2 * u) * (2 * u))

/-- Off the real axis the completed function is half the completed Fourier model. -/
theorem completedEisenstein_eq_lineModel {u : ℂ} (him : u.im ≠ 0) (x Y : ℝ) :
    completedEisenstein u x Y = lineModel u x Y / 2 := by
  have him1 : (1 + 2 * u).im ≠ 0 := by simpa using him
  have him2 : (2 * u).im ≠ 0 := by simpa using him
  have hu0 : u ≠ 0 := fun h => him (by rw [h]; simp)
  have h2u : (2 : ℂ) * u ≠ 0 := mul_ne_zero two_ne_zero hu0
  have h1 : (1 : ℂ) + 2 * u ≠ 0 := fun h => him1 (by rw [h]; simp)
  have h2 : (2 : ℂ) * u - 1 ≠ 0 := fun h => him2 (by rw [show (2 : ℂ) * u = 1 by linear_combination h]; simp)
  have hx1 := xi_eq_reflectedCompletedLambda him1
  have hx2 := xi_eq_reflectedCompletedLambda him2
  rw [show (1 : ℂ) + 2 * u - 1 = 2 * u by ring] at hx1
  rw [completedEisenstein, lineModel_eq, eisensteinNumerator, hx1, hx2]
  field_simp
  ring

/-- The completed Fourier model is even off the real axis. -/
theorem lineModel_neg {u : ℂ} (him : u.im ≠ 0) (x Y : ℝ) : lineModel (-u) x Y = lineModel u x Y := by
  rw [lineModel_eq_cuspLeg, lineModel_eq_cuspLeg, cuspLeg_neg him]

theorem differentiableAt_completed (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : u ≠ 1 / 2) (h0 : u ≠ 0)
    (hm : u ≠ -(1 / 2)) : DifferentiableAt ℂ (fun v => completedEisenstein v x Y) u := by
  have hden : (1 + 2 * u) * (2 * u) ≠ 0 :=
    mul_ne_zero (fun h => hm (by linear_combination h / 2)) (mul_ne_zero two_ne_zero h0)
  exact (differentiableAt_numerator x hY hu).div (by fun_prop) hden

/-- **The functional equation** `E*(-u) = E*(u)` for every `u ∉ {0, ±½}`. -/
theorem completedEisenstein_neg (x : ℝ) {Y : ℝ} (hY : 0 < Y) {u : ℂ} (hu : u ≠ 1 / 2) (h0 : u ≠ 0)
    (hm : u ≠ -(1 / 2)) : completedEisenstein (-u) x Y = completedEisenstein u x Y := by
  set S : Set ℂ := {0, 1 / 2, -(1 / 2)}
  have hS : S.Finite := by simp [S]
  have hU : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  have hmem : ∀ {v : ℂ}, v ∈ Sᶜ → v ≠ 1 / 2 ∧ v ≠ 0 ∧ v ≠ -(1 / 2) := fun {v} hv => by
    simp only [S, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hv
    exact ⟨hv.2.1, hv.1, hv.2.2⟩
  have hdf : DifferentiableOn ℂ (fun v => completedEisenstein (-v) x Y) Sᶜ := fun v hv => by
    obtain ⟨h1, h2, h3⟩ := hmem hv
    have hd := differentiableAt_completed x hY (u := -v) (fun h => h3 (by linear_combination -h))
      (neg_ne_zero.2 h2) (fun h => h1 (by linear_combination -h))
    exact (hd.comp v (differentiableAt_id.neg)).differentiableWithinAt
  have hdg : DifferentiableOn ℂ (fun v => completedEisenstein v x Y) Sᶜ := fun v hv => by
    obtain ⟨h1, h2, h3⟩ := hmem hv
    exact (differentiableAt_completed x hY h1 h2 h3).differentiableWithinAt
  have hI : I ∈ Sᶜ := by
    simp only [S, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨I_ne_zero, I_ne_half, fun h => ?_⟩
    have := congrArg Complex.im h
    simp at this
  have huS : u ∈ Sᶜ := by
    simp only [S, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨h0, hu, hm⟩
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (hdf.analyticOnNhd hU)
    (hdg.analyticOnNhd hU) (preconnected_compl_finite hS) hI (frequently_line fun ξ hξ => ?_) huS
  have him : ((ξ : ℂ) * I).im ≠ 0 := by simpa using hξ
  have him' : (-((ξ : ℂ) * I)).im ≠ 0 := by simpa using hξ
  rw [completedEisenstein_eq_lineModel him', completedEisenstein_eq_lineModel him, lineModel_neg him]

/-- The completed function is automorphic wherever it is defined. -/
theorem completedEisenstein_smul (γ : SL(2, ℤ)) (z : ℍ) {u : ℂ} (hu : u ≠ 1 / 2) :
    completedEisenstein u (γ • z).re (γ • z).im = completedEisenstein u z.re z.im := by
  rw [completedEisenstein, completedEisenstein, numerator_smul γ z hu]

end EisAuto

end GaloisForLFunctions.BlackHoleRingdown
