import GaloisForLFunctions.RHTower.DeckScatteringBounds

/-!
# The scattering operator at `s = 1/2` and `s = 1`

Write `φ_σ(s) = (Σ_u L_u(2s) L(Φ_{σ,u}, 2s − 1)) · C(s)` with `C(s) = √π Γ(s − 1/2)/Γ(s)`.

* **At `s = 1/2`.**  `L_u(w) = φ(L)⁻¹ Σ_χ χ(u⁻¹)/L(w, χ)` has a limit as `w → 1`: for `χ ≠ 1` because
  `L(1, χ) ≠ 0`, and for the trivial character because `(w − 1)L(w, 1)` tends to `Π_{p|L}(1 − 1/p) ≠ 0`.
  Since `(s − 1/2)C(s) = √π Γ(s + 1/2)/Γ(s)`, every `(s − 1/2)φ_σ(s)` has a limit at `1/2`.  For `v ∈ V_∞`
  the unitarity `‖Φ̃(1/2 + it)v‖ = ‖v‖` forces the limit of `(s − 1/2)Φ̃(s)v` to vanish, so `Φ̃(·)v` has a
  removable singularity at `1/2`: it tends to a limit as `s → 1/2`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Metric EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergEisensteinStarCriticalLine

noncomputable section

variable {N : ℕ}

/-! ## Limits of the Möbius class series at `w = 1` -/

section LLimits

variable (L : ℕ) [NeZero L]

omit [NeZero L] in
theorem prod_one_sub_inv_ne_zero : (∏ p ∈ L.primeFactors, (1 - (p : ℂ)⁻¹)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  intro h
  have h1 : ((p : ℂ))⁻¹ = 1 := by linear_combination -h
  have h2 := congrArg Complex.re h1
  simp only [Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast, Complex.one_re] at h2
  have : (p : ℝ) / (p : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  rw [show (p : ℝ) * (p : ℝ) = (p : ℝ) ^ 2 by ring] at h2
  linarith

theorem tendsto_inv_LFunction_trivial :
    Tendsto (fun w => (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ L) w)⁻¹) (𝓝[≠] 1)
      (𝓝 0) := by
  have h1 := (DirichletCharacter.LFunctionTrivChar_residue_one (N := L)).inv₀ (prod_one_sub_inv_ne_zero L)
  have h2 : Tendsto (fun w : ℂ => w - 1) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun w : ℂ => w - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have h3 := h2.mul h1
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw1 : w - 1 ≠ 0 := sub_ne_zero.2 hw
  change (w - 1) * ((w - 1) * DirichletCharacter.LFunctionTrivChar L w)⁻¹ = _
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hw1, one_mul]

theorem exists_tendsto_inv_LFunction (χ : DirichletCharacter ℂ L) :
    ∃ ℓ, Tendsto (fun w => (DirichletCharacter.LFunction χ w)⁻¹) (𝓝[≠] 1) (𝓝 ℓ) := by
  by_cases hχ : χ = 1
  · subst hχ; exact ⟨0, tendsto_inv_LFunction_trivial L⟩
  · refine ⟨(DirichletCharacter.LFunction χ 1)⁻¹, ?_⟩
    exact ((DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr hχ)).continuousAt.tendsto.inv₀
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ)).mono_left nhdsWithin_le_nhds

theorem exists_tendsto_LU (u : (ZMod L)ˣ) :
    ∃ ℓ, Tendsto (fun w => SelbergMoebiusUnitClassL.LU L u w) (𝓝[≠] 1) (𝓝 ℓ) := by
  choose ℓ hℓ using exists_tendsto_inv_LFunction L
  refine ⟨(L.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ L, χ ((u : ZMod L)⁻¹) * ℓ χ, ?_⟩
  unfold SelbergMoebiusUnitClassL.LU
  exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun χ _ => tendsto_const_nhds.mul (hℓ χ))

/-- `L(w, χ) ≠ 0` on a punctured neighbourhood of `w = 1`. -/
theorem eventually_LFunction_ne_zero (χ : DirichletCharacter ℂ L) :
    ∀ᶠ w in 𝓝[≠] (1 : ℂ), DirichletCharacter.LFunction χ w ≠ 0 := by
  by_cases hχ : χ = 1
  · subst hχ
    have h := (DirichletCharacter.LFunctionTrivChar_residue_one (N := L)).eventually_ne
      (prod_one_sub_inv_ne_zero L)
    filter_upwards [h] with w hw h0
    have h0' : DirichletCharacter.LFunctionTrivChar L w = 0 := h0
    rw [h0', mul_zero] at hw
    exact hw rfl
  · exact ((DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr hχ)).continuousAt.eventually_ne
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ)).filter_mono nhdsWithin_le_nhds

end LLimits

/-! ## The scattering entries near `s = 1/2` -/

theorem tendsto_two_mul_half :
    Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun s : ℂ => 2 * s) (𝓝 (1 / 2)) (𝓝 (2 * (1 / 2))) :=
      (continuous_const.mul continuous_id).tendsto _
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs h
    have h' : 2 * s = 1 := h
    exact hs (Set.mem_singleton_iff.2 (by linear_combination h' / 2))

theorem exists_tendsto_sub_half_mul_cBeta :
    ∃ ℓ, Tendsto (fun s : ℂ => (s - 1 / 2) * SelbergKernelBetaIntegral.cBeta s) (𝓝[≠] (1 / 2)) (𝓝 ℓ) := by
  refine ⟨(Real.sqrt Real.pi : ℂ) * Complex.Gamma (1 / 2 + 1 / 2) * (Complex.Gamma (1 / 2))⁻¹, ?_⟩
  have hΓ : DifferentiableAt ℂ Complex.Gamma (1 / 2 + 1 / 2) := by
    refine Complex.differentiableAt_Gamma _ fun m hm => ?_
    have := congrArg Complex.re hm
    norm_num at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hΓ1 : ContinuousAt (fun s : ℂ => Complex.Gamma (s + 1 / 2)) (1 / 2) :=
    ContinuousAt.comp (g := Complex.Gamma) (f := fun s : ℂ => s + 1 / 2) hΓ.continuousAt
      (continuousAt_id.add continuousAt_const)
  have hΓinv : ContinuousAt (fun s : ℂ => (Complex.Gamma s)⁻¹) (1 / 2) := by
    have := (Complex.differentiable_one_div_Gamma (1 / 2)).continuousAt
    simpa [one_div] using this
  have hc : ContinuousAt (fun s : ℂ => (Real.sqrt Real.pi : ℂ) * Complex.Gamma (s + 1 / 2) *
      (Complex.Gamma s)⁻¹) (1 / 2) := (continuousAt_const.mul hΓ1).mul hΓinv
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - 1 / 2 ≠ 0 := sub_ne_zero.2 hs
  unfold SelbergKernelBetaIntegral.cBeta
  have hg := Complex.Gamma_add_one (s - 1 / 2) hs'
  rw [show s - 1 / 2 + 1 = s + 1 / 2 by ring] at hg
  rw [hg]
  ring

/-- Every `(s − 1/2) φ_σ(s)` has a limit at `s = 1/2`. -/
theorem exists_tendsto_sub_half_mul_phiExt (σ : SL(2, ℤ)) :
    ∃ ℓ, Tendsto (fun s : ℂ => (s - 1 / 2) * SelbergEisensteinCriticalLine.phiExt (N + 1) σ s)
      (𝓝[≠] (1 / 2)) (𝓝 ℓ) := by
  obtain ⟨ℓC, hC⟩ := exists_tendsto_sub_half_mul_cBeta
  choose ℓU hU using exists_tendsto_LU (N + 1)
  have hZ : ∀ u : (ZMod (N + 1))ˣ, Tendsto (fun s : ℂ => ZMod.LFunction
      (SelbergEisensteinCuspScattering.PhiU (N + 1) (SelbergEisensteinCuspScattering.PhiS (N + 1) σ) u)
        (2 * s - 1)) (𝓝[≠] (1 / 2)) (𝓝 (ZMod.LFunction
          (SelbergEisensteinCuspScattering.PhiU (N + 1) (SelbergEisensteinCuspScattering.PhiS (N + 1) σ) u)
            (2 * (1 / 2) - 1))) := fun u => by
    refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
    refine (ZMod.differentiableAt_LFunction _ _ (Or.inl ?_)).continuousAt.comp
      ((continuousAt_const.mul continuousAt_id).sub continuousAt_const)
    norm_num
  refine ⟨(∑ u : (ZMod (N + 1))ˣ, ℓU u * ZMod.LFunction
    (SelbergEisensteinCuspScattering.PhiU (N + 1) (SelbergEisensteinCuspScattering.PhiS (N + 1) σ) u)
      (2 * (1 / 2) - 1)) * ℓC, ?_⟩
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ZMod (N + 1))ˣ) fun u _ =>
    ((hU u).comp tendsto_two_mul_half).mul (hZ u)
  refine (hsum.mul hC).congr' (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, SelbergEisensteinCriticalLine.phiExt]
  ring

/-! ## The removable singularity of `Φ̃(·)v` at `1/2` -/

/-- A punctured neighbourhood of `1/2` lies in the continuation domain. -/
theorem eventually_mem_contDom_half : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s ∈ contDom N := by
  have hW : ∀ χ : DirichletCharacter ℂ (N + 1),
      ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), DirichletCharacter.LFunction χ (2 * s) ≠ 0 :=
    fun χ => tendsto_two_mul_half.eventually (eventually_LFunction_ne_zero (N + 1) χ)
  have hall := Filter.eventually_all.2 hW
  have hre0 : ∀ᶠ s in 𝓝 (1 / 2 : ℂ), 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (0 : ℝ) < (1 / 2 : ℂ).re by norm_num)
  have hre : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), 0 < s.re := hre0.filter_mono nhdsWithin_le_nhds
  have hne1 : ∀ᶠ s in 𝓝[≠] (1 / 2 : ℂ), s ≠ 1 :=
    (continuousAt_id.eventually_ne (show (1 / 2 : ℂ) ≠ 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hall, hre, hne1, self_mem_nhdsWithin] with s h1 h2 h3 h4
  refine ⟨⟨h2, fun h => h4 (Set.mem_singleton_iff.2 (by linear_combination h / 2)), h1⟩, h3⟩

/-- The line map `t ↦ 1/2 + it` sends punctured neighbourhoods of `0` into punctured neighbourhoods
of `1/2`. -/
theorem tendsto_line_half :
    Tendsto (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (𝓝[≠] 0) (𝓝[≠] (1 / 2 : ℂ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) (𝓝 0)
        (𝓝 (((1 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht h
    have := congrArg Complex.im (Set.mem_singleton_iff.1 h)
    simp at this
    exact ht (Set.mem_singleton_iff.2 this)

/-- **`(s − 1/2) Φ̃(s) v → 0`** for `v ∈ V_∞`. -/
theorem tendsto_sub_half_mul_scatVec_apply (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v)
    (q : Deck N) :
    Tendsto (fun s : ℂ => (s - 1 / 2) * scatVec s v q) (𝓝[≠] (1 / 2)) (𝓝 0) := by
  choose ℓ hℓ using fun g : Deck N => exists_tendsto_sub_half_mul_phiExt (N := N) (Quotient.out g)
  have hlim : Tendsto (fun s : ℂ => (s - 1 / 2) * scatVec s v q) (𝓝[≠] (1 / 2))
      (𝓝 ((2 * (N + 1 : ℂ) ^ 2)⁻¹ * ∑ g : Deck N, ℓ g * v (q * g⁻¹))) := by
    refine (tendsto_const_nhds.mul (tendsto_finsetSum _ fun g _ => (hℓ g).mul
      tendsto_const_nhds)).congr' (Eventually.of_forall fun s => ?_)
    simp only [scatVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hline : Tendsto (fun t : ℝ => ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1 / 2) *
      scatVec (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) v q) (𝓝[≠] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), ‖((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1 / 2) *
        scatVec (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) v q‖ ≤ |t| * ‖v‖ := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      rw [norm_mul, show (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1 / 2 = (t : ℂ) * Complex.I by
        push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le _ q).trans (le_of_eq ?_)) (abs_nonneg t)
      exact norm_scatVec_line hN ht0 hv
    have h0 : Tendsto (fun t : ℝ => |t| * ‖v‖) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => |t| * ‖v‖) (𝓝 0) (𝓝 (|0| * ‖v‖)) :=
        (continuous_abs.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) hb h0
  have h2 := hlim.comp tendsto_line_half
  rw [tendsto_nhds_unique h2 hline] at hlim
  exact hlim

/-- **The removable singularity at `1/2`**: `Φ̃(s)v` tends to a limit as `s → 1/2`. -/
theorem exists_tendsto_scatVec_half (hN : 2 ≤ N) {v : DeckSpace N} (hv : IsCuspVec v) :
    ∃ w₀ : DeckSpace N, Tendsto (fun s : ℂ => scatVec s v) (𝓝[≠] (1 / 2)) (𝓝 w₀) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (eventually_mem_contDom_half (N := N)))
  have hcoord : ∀ q : Deck N, ∃ ℓ, Tendsto (fun s : ℂ => scatVec s v q) (𝓝[≠] (1 / 2)) (𝓝 ℓ) := by
    intro q
    set f : ℂ → ℂ := fun s => scatVec s v q
    have hdiff : DifferentiableOn ℂ f (ball (1 / 2 : ℂ) δ \ {1 / 2}) := fun s hs =>
      (differentiableAt_scatVec_apply v q (hball hs.1 hs.2).1 (hball hs.1 hs.2).2).differentiableWithinAt
    have hsmall : (fun z => f z - f (1 / 2)) =o[𝓝[≠] (1 / 2 : ℂ)] fun z => (z - 1 / 2)⁻¹ := by
      have hg : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), (z - 1 / 2)⁻¹ = 0 → f z - f (1 / 2) = 0 := by
        filter_upwards [self_mem_nhdsWithin] with z hz h0
        exact absurd h0 (inv_ne_zero (sub_ne_zero.2 hz))
      rw [Asymptotics.isLittleO_iff_tendsto' hg]
      have hA := tendsto_sub_half_mul_scatVec_apply hN hv q
      have hB : Tendsto (fun z : ℂ => (z - 1 / 2) * f (1 / 2)) (𝓝[≠] (1 / 2)) (𝓝 0) := by
        have : Tendsto (fun z : ℂ => (z - 1 / 2) * f (1 / 2)) (𝓝 (1 / 2))
            (𝓝 ((1 / 2 - 1 / 2) * f (1 / 2))) :=
          ((continuous_id.sub continuous_const).mul continuous_const).tendsto _
        simpa using this.mono_left nhdsWithin_le_nhds
      have h := hA.sub hB
      rw [sub_self] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - 1 / 2 ≠ 0 := sub_ne_zero.2 hz
      simp only [f]
      field_simp
    have hF := Complex.differentiableOn_update_limUnder_of_isLittleO (ball_mem_nhds _ hδ) hdiff hsmall
    have hc : ContinuousAt (Function.update f (1 / 2) ((𝓝[≠] (1 / 2 : ℂ)).limUnder f)) (1 / 2) :=
      (hF.differentiableAt (ball_mem_nhds _ hδ)).continuousAt
    refine ⟨_, (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Function.update_of_ne hz _ _
  choose ℓ hℓ using hcoord
  refine ⟨WithLp.toLp 2 ℓ, ?_⟩
  have e : (fun s : ℂ => scatVec s v) = fun s => WithLp.toLp 2 (fun q => scatVec s v q) :=
    funext fun s => rfl
  rw [e]
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 hℓ)

/-! ## The residue at `s = 1` -/

theorem sum_PhiU_PhiS (L : ℕ) [NeZero L] (σ : SL(2, ℤ)) (u : (ZMod L)ˣ) :
    ∑ j : ZMod L, SelbergEisensteinCuspScattering.PhiU L (SelbergEisensteinCuspScattering.PhiS L σ) u j = 2 := by
  unfold SelbergEisensteinCuspScattering.PhiU
  rw [show (∑ j : ZMod L, SelbergEisensteinCuspScattering.PhiS L σ ((u : ZMod L) * j)) =
      ∑ j : ZMod L, SelbergEisensteinCuspScattering.PhiS L σ j from
    Equiv.sum_comp (Units.mulLeft u) (SelbergEisensteinCuspScattering.PhiS L σ)]
  unfold SelbergEisensteinCuspScattering.PhiS
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  norm_num

/-- The common residue `ρ₁ = cBeta(1) · Σ_u L_u(2) / L` of the scattering entries at `s = 1`. -/
def scatResidue (N : ℕ) : ℂ :=
  (∑ u : (ZMod (N + 1))ˣ, SelbergMoebiusUnitClassL.LU (N + 1) u 2) *
    SelbergKernelBetaIntegral.cBeta 1 / (N + 1 : ℂ)

theorem tendsto_two_mul_sub_one :
    Tendsto (fun s : ℂ => 2 * s - 1) (𝓝[≠] (1 : ℂ)) (𝓝[≠] 1) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun s : ℂ => 2 * s - 1) (𝓝 1) (𝓝 (2 * 1 - 1)) :=
      ((continuous_const.mul continuous_id).sub continuous_const).tendsto _
    rw [show (2 : ℂ) * 1 - 1 = 1 by norm_num] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs h
    have h' : 2 * s - 1 = 1 := h
    exact hs (Set.mem_singleton_iff.2 (by linear_combination h' / 2))

/-- **Every scattering entry has the same residue at `s = 1`.** -/
theorem tendsto_sub_one_mul_phiExt (σ : SL(2, ℤ)) :
    Tendsto (fun s : ℂ => (s - 1) * SelbergEisensteinCriticalLine.phiExt (N + 1) σ s) (𝓝[≠] 1)
      (𝓝 (scatResidue N)) := by
  have hL2 : ∀ u : (ZMod (N + 1))ˣ, Tendsto (fun s : ℂ => SelbergMoebiusUnitClassL.LU (N + 1) u (2 * s))
      (𝓝[≠] 1) (𝓝 (SelbergMoebiusUnitClassL.LU (N + 1) u 2)) := fun u => by
    have hd := SelbergEisensteinCoefficientSeries.differentiableAt_LU_of (N + 1) u
      (show (2 : ℂ) ≠ 1 by norm_num) fun χ =>
        DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
    have hd' : ContinuousAt (SelbergMoebiusUnitClassL.LU (N + 1) u) ((fun s : ℂ => 2 * s) 1) := by
      simpa using hd.continuousAt
    have := (ContinuousAt.comp hd' (continuous_const.mul continuous_id).continuousAt).tendsto
    simp only [Function.comp_def, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hZ : ∀ u : (ZMod (N + 1))ˣ, Tendsto (fun s : ℂ => (s - 1) * ZMod.LFunction
      (SelbergEisensteinCuspScattering.PhiU (N + 1) (SelbergEisensteinCuspScattering.PhiS (N + 1) σ) u)
        (2 * s - 1)) (𝓝[≠] 1) (𝓝 (1 / (N + 1 : ℂ))) := fun u => by
    have h := ((ZMod.LFunction_residue_one (N := N + 1)
      (SelbergEisensteinCuspScattering.PhiU (N + 1) (SelbergEisensteinCuspScattering.PhiS (N + 1) σ) u)).comp
        tendsto_two_mul_sub_one).const_mul (1 / 2 : ℂ)
    have hsum : ∑ j, SelbergEisensteinCuspScattering.PhiU (N + 1)
        (SelbergEisensteinCuspScattering.PhiS (N + 1) σ) u j / ((N + 1 : ℕ) : ℂ) = 2 / (N + 1 : ℂ) := by
      rw [← Finset.sum_div, sum_PhiU_PhiS]; push_cast; ring
    rw [hsum] at h
    refine (h.congr' (Eventually.of_forall fun s => ?_)).trans ?_
    · simp only [Function.comp_apply]; ring
    · rw [show (1 / 2 : ℂ) * (2 / (N + 1 : ℂ)) = 1 / (N + 1 : ℂ) by ring]
  have hC : Tendsto SelbergKernelBetaIntegral.cBeta (𝓝[≠] 1) (𝓝 (SelbergKernelBetaIntegral.cBeta 1)) := by
    refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
    have hΓ : ContinuousAt (fun s : ℂ => Complex.Gamma (s - 1 / 2)) 1 := by
      refine ContinuousAt.comp (g := Complex.Gamma) (f := fun s : ℂ => s - 1 / 2) ?_
        (continuousAt_id.sub continuousAt_const)
      refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).continuousAt
      have := congrArg Complex.re hm
      norm_num at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hΓinv : ContinuousAt (fun s : ℂ => (Complex.Gamma s)⁻¹) 1 := by
      simpa [one_div] using (Complex.differentiable_one_div_Gamma 1).continuousAt
    exact (continuousAt_const.mul hΓ).mul hΓinv
  have hsum := tendsto_finsetSum (Finset.univ : Finset (ZMod (N + 1))ˣ) fun u _ => (hL2 u).mul (hZ u)
  have hval : (∑ u : (ZMod (N + 1))ˣ, SelbergMoebiusUnitClassL.LU (N + 1) u 2 * (1 / (N + 1 : ℂ))) *
      SelbergKernelBetaIntegral.cBeta 1 = scatResidue N := by
    rw [← Finset.sum_mul]
    unfold scatResidue
    ring
  have h := hsum.mul hC
  rw [hval] at h
  refine h.congr' (Eventually.of_forall fun s => ?_)
  simp only [SelbergEisensteinCriticalLine.phiExt, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- The all-ones deck vector. -/
def onesVec (N : ℕ) : DeckSpace N := WithLp.toLp 2 fun _ => 1

/-- **The residue of `Φ̃` at `s = 1`**: `(s − 1)Φ̃(s)v → (2L²)⁻¹ ρ₁ (Σ_x v_x) · 𝟙`. -/
theorem tendsto_sub_one_smul_scatVec (v : DeckSpace N) :
    Tendsto (fun s : ℂ => (s - 1) • scatVec s v) (𝓝[≠] 1)
      (𝓝 (((2 * (N + 1 : ℂ) ^ 2)⁻¹ * scatResidue N * ∑ x : Deck N, v x) • onesVec N)) := by
  have hcoord : ∀ q : Deck N, Tendsto (fun s : ℂ => ((s - 1) • scatVec s v) q) (𝓝[≠] 1)
      (𝓝 ((((2 * (N + 1 : ℂ) ^ 2)⁻¹ * scatResidue N * ∑ x : Deck N, v x) • onesVec N) q)) := by
    intro q
    have h := (tendsto_const_nhds (x := (2 * (N + 1 : ℂ) ^ 2)⁻¹)).mul
      (tendsto_finsetSum (Finset.univ : Finset (Deck N)) fun g _ =>
      (tendsto_sub_one_mul_phiExt (N := N) (Quotient.out g)).mul_const (v (q * g⁻¹)))
    refine (h.congr' (Eventually.of_forall fun s => ?_)).trans ?_
    · change (2 * (N + 1 : ℂ) ^ 2)⁻¹ * ∑ g : Deck N, (s - 1) *
          SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s * v (q * g⁻¹) =
        (s - 1) * scatVec s v q
      rw [scatVec_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by ring
    · have hre : ∑ g : Deck N, scatResidue N * v (q * g⁻¹) = scatResidue N * ∑ x : Deck N, v x := by
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp ((Equiv.inv (Deck N)).trans (Equiv.mulLeft q)) v
      rw [hre]
      change 𝓝 ((2 * (N + 1 : ℂ) ^ 2)⁻¹ * (scatResidue N * ∑ x : Deck N, v x)) ≤
        𝓝 (((2 * (N + 1 : ℂ) ^ 2)⁻¹ * scatResidue N * ∑ x : Deck N, v x) * 1)
      rw [mul_one, mul_assoc]
  have e : (fun s : ℂ => (s - 1) • scatVec s v) = fun s => WithLp.toLp 2 (fun q => ((s - 1) • scatVec s v) q) :=
    funext fun s => rfl
  rw [e]
  exact ((PiLp.continuous_toLp 2 _).tendsto _).comp (tendsto_pi_nhds.2 hcoord)

end

end GaloisForLFunctions.RHTower.DeckPointPair
