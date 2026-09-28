import GaloisForLFunctions.RHTower.ChronologicalTailWeight
import GaloisForLFunctions.RHTower.ChronologicalWeightedBoundary
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem

/-!
# A fixed smooth tail space cannot repair a proportional Möbius prefix

Fix `0 < θ < 1` and a finite-dimensional real space `V` of functions Lipschitz on `[θ, 1]`
(for instance a finite-dimensional subspace of `C¹([θ, 1])`).  For `f ∈ V` the array
`a_k = μ(k)` (`k ≤ θN`), `a_k = f(k/N)` (`θN < k ≤ N`) has actual residual

  `r_{N,f}(t) = e^{-t} + Σ_{k ≤ N} a_k h(kt)`,  `h(t) = 1/t - 1/(e^t - 1)`.

**Theorem.** There is `ε > 0` with `‖r_{N,f}‖_{L²(0,∞)} ≥ ε` for arbitrarily large `N`, uniformly
over all `f ∈ V`; no bound on the tail coefficients is assumed.

**Positive survivor.** For every critical zeta zero `ρ`, the component of the critical profile
`K_ρ(u) = ∫_0^θ x^{ρ-1} h(xu) dx` orthogonal to the tail heat space
`W = span_ℂ {∫_θ¹ f(x) h(xu) dx : f ∈ V}` in `L²([1, 2])` has norm `d = dist(K_ρ, W) > 0`, and a
uniform observation inequality bounds the Möbius source seen by the unit normal through the actual
residual.  Consequently, if `‖r_{N,f_N}‖ ≤ L` for all large `N`, then `d ≤ L |ζ'(ρ)|`; at a
multiple critical zero no bounded family exists.

The proof uses one Hardy zero on the critical line, heat-transform separation, `O(1/N)` exact
discrete projections, the Möbius Dirichlet identity through the quantitative critical boundary
of weighted Möbius sources, and no numerical input.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology Moebius

noncomputable section

namespace RHTower

/-! ### Restriction bases -/

/-- A finite-dimensional space of functions has a finite family in it whose restrictions to `s`
are linearly independent and span the restrictions of the whole space. -/
theorem exists_restriction_basis (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V] (s : Set ℝ) :
    ∃ (l : ℕ) (g : Fin l → ℝ → ℝ), (∀ i, g i ∈ V) ∧
      (∀ c : Fin l → ℝ, (∀ x ∈ s, ∑ i, c i * g i x = 0) → c = 0) ∧
      ∀ f ∈ V, ∃ c : Fin l → ℝ, ∀ x ∈ s, f x = ∑ i, c i * g i x := by
  set R : V →ₗ[ℝ] (s → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Subtype.val : s → ℝ)).comp V.subtype with hR
  have hRapp : ∀ (v : V) (x : s), R v x = (v : ℝ → ℝ) x := fun _ _ => rfl
  set U := LinearMap.range R
  haveI : FiniteDimensional ℝ U := LinearMap.finiteDimensional_range R
  set b := Module.finBasis ℝ U
  have hpre : ∀ i, ∃ v : V, R v = (b i : s → ℝ) := fun i => LinearMap.mem_range.mp (b i).2
  choose v hv using hpre
  refine ⟨Module.finrank ℝ U, fun i => (v i : ℝ → ℝ), fun i => (v i).2, ?_, ?_⟩
  · intro c hc
    have hsum : ∑ i, c i • b i = 0 := by
      apply Subtype.ext
      funext x
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
      rw [← hc x x.2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hv i, hRapp]
    exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hsum)
  · intro f hf
    set u : U := ⟨R ⟨f, hf⟩, LinearMap.mem_range_self R _⟩ with hu
    refine ⟨fun i => b.repr u i, fun x hx => ?_⟩
    have h := congrArg (fun z : U => (z : s → ℝ) ⟨x, hx⟩) (b.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    rw [show (u : s → ℝ) ⟨x, hx⟩ = f x from rfl] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hv i, hRapp]

/-! ### The tail heat space and the fixed-tail defect -/

/-- The complex span in `L²([1, 2])` of the tail heat vectors of a space of tail profiles. -/
def tailSpan (θ : ℝ) (V : Submodule ℝ (ℝ → ℝ)) : Submodule ℂ SampleSpace :=
  Submodule.span ℂ (tailVec θ '' (V : Set (ℝ → ℝ)))

/-- The fixed-tail defect `d = dist(K_ρ, W)`: the part of the critical profile the tail space
cannot absorb. -/
def fixedTailDefect (θ : ℝ) (V : Submodule ℝ (ℝ → ℝ)) (ρ : ℂ) : ℝ :=
  Metric.infDist (critVec θ ρ) (tailSpan θ V : Set SampleSpace)

theorem tailSpan_eq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {V : Submodule ℝ (ℝ → ℝ)} {l : ℕ}
    {g : Fin l → ℝ → ℝ} (hgV : ∀ i, g i ∈ V) (hcont : ∀ i, ContinuousOn (g i) (Icc θ 1))
    (hspan : ∀ f ∈ V, ∃ c : Fin l → ℝ, ∀ x ∈ Icc θ 1, f x = ∑ i, c i * g i x) :
    tailSpan θ V = Submodule.span ℂ (Set.range fun i => tailVec θ (g i)) := by
  apply le_antisymm
  · rw [tailSpan, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨c, hc⟩ := hspan f hf
    have hvec : tailVec θ f = ∑ i, (c i : ℂ) • tailVec θ (g i) := by
      rw [sum_smul_tailVec hθ0 hθ1 hcont, tailVec]
      congr 1
      funext u
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hθ1.le] at hx
      simp only [hc x hx, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [SetLike.mem_coe, hvec]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨g i, hgV i, rfl⟩

/-! ### The observation inequality -/

/-- **Uniform observation inequality.**  For every critical `ρ` there is a unit sampling functional
`ψ` whose weighted Möbius source has Mellin moment `d = dist(K_ρ, W) > 0` at `ρ`, and whose source
at the integer scale `1/N` is controlled by the actual residual of every tail in `V`. -/
theorem exists_observation_inequality {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ f ∈ V, ∃ K, LipschitzOnWith K f (Icc θ 1)) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ∃ ψ : SampleSpace, ‖ψ‖ = 1 ∧ mellin (observedWeight θ ψ) ρ = (fixedTailDefect θ V ρ : ℂ) ∧
      0 < fixedTailDefect θ V ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N₁ : ℕ, 0 < N₁ ∧ ∀ N : ℕ, N₁ ≤ N → ∀ f ∈ V,
        ‖chronologicalMobiusWeightedSource (observedWeight θ ψ) (1 / N)‖ ≤
          Real.sqrt N * chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) + C := by
  obtain ⟨l, g, hgV, hind, hspan⟩ := exists_restriction_basis V (Icc θ 1)
  choose K hK using fun i => hV (g i) (hgV i)
  have hcont : ∀ i, ContinuousOn (g i) (Icc θ 1) := fun i => (hK i).continuousOn
  obtain ⟨ψ, hψ1, -, hψK, hdpos, C, N₁, hN₁, hψN⟩ := exists_tail_normals hθ0 hθ1 hρ hK hind
  have hd : fixedTailDefect θ V ρ = Metric.infDist (critVec θ ρ)
      (Submodule.span ℂ (Set.range fun i => tailVec θ (g i)) : Set SampleSpace) := by
    rw [fixedTailDefect, tailSpan_eq hθ0 hθ1 hgV hcont hspan]
  have hC0 : 0 ≤ C := by
    obtain ⟨ψN, -, -, hdist⟩ := hψN N₁ le_rfl
    have hN₁r : (0 : ℝ) < N₁ := by exact_mod_cast hN₁
    exact (div_nonneg_iff.mp ((norm_nonneg _).trans hdist)).elim (fun h => h.1)
      fun h => absurd h.2 (not_le.mpr hN₁r)
  refine ⟨ψ, hψ1, by rw [mellin_observedWeight hθ1 ψ hρ, hψK, hd], hd ▸ hdpos, 1 + C, by linarith,
    N₁, hN₁, fun N hN f hfV => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le hN₁ hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨c, hc⟩ := hspan f hfV
  obtain ⟨ψN, hψN1, hψNperp, hψNdist⟩ := hψN N hN
  have hobsN := norm_inner_headFun_le hNpos hψN1 hψNperp hc
  rw [← inner_headFun_eq_source hθ1 ψ hNpos]
  have hsplit : (inner ℂ ψ (toSample (headFun θ N)) : ℂ) =
      inner ℂ ψN (toSample (headFun θ N)) + inner ℂ (ψ - ψN) (toSample (headFun θ N)) := by
    rw [inner_sub_left]; ring
  have hdiff : ‖(inner ℂ (ψ - ψN) (toSample (headFun θ N)) : ℂ)‖ ≤ C := by
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖ψ - ψN‖ * ‖toSample (headFun θ N)‖ ≤ (C / N) * N :=
          mul_le_mul (by rw [norm_sub_rev]; exact hψNdist) (norm_toSample_headFun_le θ N)
            (norm_nonneg _) (div_nonneg hC0 hNr.le)
      _ = C := by field_simp
  rw [hsplit]
  calc _ ≤ ‖(inner ℂ ψN (toSample (headFun θ N)) : ℂ)‖ +
        ‖(inner ℂ (ψ - ψN) (toSample (headFun θ N)) : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### The quantitative obstruction -/

/-- **The fixed-tail defect is positive and bounds every eventual residual level.**  If for all large
`N` some `f ∈ V` has `‖r_{N,f}‖ ≤ L`, then `dist(K_ρ, W) ≤ L |ζ'(ρ)|` at every critical zero `ρ`. -/
theorem tailDefect_pos_and_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ f ∈ V, ∃ K, LipschitzOnWith K f (Icc θ 1)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : riemannZeta ρ = 0) :
    0 < fixedTailDefect θ V ρ ∧ ∀ L : ℝ, (∀ᶠ N : ℕ in atTop, ∃ f ∈ V,
      chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) ≤ L) →
        fixedTailDefect θ V ρ ≤ L * ‖deriv riemannZeta ρ‖ := by
  obtain ⟨ψ, hψ1, hmellin, hdpos, C, hC0, N₁, hN₁, hobs⟩ :=
    exists_observation_inequality hθ0 hθ1 V hV hρ
  refine ⟨hdpos, fun L hL => ?_⟩
  set d := fixedTailDefect θ V ρ with hddef
  set w := observedWeight θ ψ with hw
  have hwm : Measurable w := measurable_observedWeight hθ1.le ψ
  have hwb : ∀ x, 0 < x → ‖w x‖ ≤ 1 := fun x _ => by
    rw [hw, observedWeight]
    by_cases hx : x ∈ Ioc 0 θ
    · rw [Set.indicator_of_mem hx]; exact (norm_sampleProfile_le ψ x).trans hψ1.le
    · rw [Set.indicator_of_notMem hx, norm_zero]; exact zero_le_one
  have hwtop : ∀ x, 1 < x → w x = 0 := fun x hx =>
    Set.indicator_of_notMem (fun h => by linarith [h.2]) _
  have hnormM : ‖mellin w ρ‖ = d := by
    rw [hw, hmellin, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdpos]
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hL
  have hL0 : 0 ≤ L := by
    obtain ⟨f, -, hf⟩ := hN₂ N₂ le_rfl
    exact (chronologicalL2Norm_nonneg _).trans hf
  -- the source at integer scales
  set N₃ := max N₁ N₂ with hN₃
  have hint : ∀ N : ℕ, N₃ ≤ N →
      ‖chronologicalMobiusWeightedSource w (1 / N)‖ ≤ Real.sqrt N * L + C := by
    intro N hN
    obtain ⟨f, hfV, hfL⟩ := hN₂ N (le_trans (le_max_right _ _) hN)
    exact (hobs N (le_trans (le_max_left _ _) hN) f hfV).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hfL (Real.sqrt_nonneg N)])
  -- the source at real scales
  obtain ⟨L₀, hL₀0, hL₀⟩ := exists_sampleProfile_lipschitz
  have hreal : ∀ t : ℝ, 0 < t → t ≤ 1 / (N₃ + 1 : ℕ) →
      ‖chronologicalMobiusWeightedSource w t‖ ≤ L * t ^ (-(1 / 2 : ℝ)) + (C + (L₀ + 1)) := by
    intro t ht htN
    have hN3r : (0 : ℝ) < ((N₃ + 1 : ℕ) : ℝ) := by positivity
    have hinv : ((N₃ + 1 : ℕ) : ℝ) ≤ 1 / t := by
      rw [le_div_iff₀ ht]; rw [le_div_iff₀ hN3r] at htN; linarith
    have ht1 : t ≤ 1 := by
      refine htN.trans ((div_le_one hN3r).mpr ?_)
      exact_mod_cast Nat.succ_pos N₃
    set N := ⌊1 / t⌋₊ with hNdef
    have hNge : N₃ + 1 ≤ N := Nat.le_floor hinv
    have hNle : (N : ℝ) ≤ 1 / t := Nat.floor_le (by positivity)
    have htrans := norm_chronologicalMobiusWeightedSource_sub_floor_le hθ0 hθ1 (H := sampleProfile ψ)
      (L := L₀) (B := 1) hL₀0 zero_le_one
      (fun x _ => (norm_sampleProfile_le ψ x).trans hψ1.le)
      (fun x hx y hy => by
        simpa [hψ1] using hL₀ ψ x ⟨hx.1, hx.2.trans hθ1.le⟩ y ⟨hy.1, hy.2.trans hθ1.le⟩)
      ht ht1
    have hsqrt : Real.sqrt N ≤ t ^ (-(1 / 2 : ℝ)) := by
      calc Real.sqrt N ≤ Real.sqrt (1 / t) := Real.sqrt_le_sqrt hNle
        _ = t ^ (-(1 / 2 : ℝ)) := by
          rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg ht.le]
    have hN := hint N (by omega)
    have htrans' : ‖chronologicalMobiusWeightedSource w t -
        chronologicalMobiusWeightedSource w (1 / N)‖ ≤ L₀ + 1 := htrans
    calc ‖chronologicalMobiusWeightedSource w t‖
        ≤ ‖chronologicalMobiusWeightedSource w (1 / N)‖ + (L₀ + 1) := by
          have := norm_sub_norm_le (chronologicalMobiusWeightedSource w t)
            (chronologicalMobiusWeightedSource w (1 / N))
          linarith
      _ ≤ Real.sqrt N * L + C + (L₀ + 1) := by linarith
      _ ≤ L * t ^ (-(1 / 2 : ℝ)) + (C + (L₀ + 1)) := by
          nlinarith [mul_le_mul_of_nonneg_right hsqrt hL0]
  -- the quantitative Mellin boundary
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set D := ‖deriv riemannZeta ρ‖ with hD
  have hη : 0 < ε / (D + 1) := by positivity
  set C₄ := C + (L₀ + 1) with hC₄
  have hC₄0 : 0 ≤ C₄ := by positivity
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖chronologicalMobiusWeightedSource w t‖ ≤
      (L + ε / (D + 1)) * t ^ (-(1 / 2 : ℝ)) := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 / (N₃ + 1 : ℕ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    have hlarge : ∀ᶠ t : ℝ in 𝓝[>] 0, C₄ / (ε / (D + 1)) ≤ t ^ (-(1 / 2 : ℝ)) :=
      (tendsto_rpow_neg_nhdsGT_zero (by norm_num : -(1 / 2 : ℝ) < 0)).eventually_ge_atTop _
    filter_upwards [self_mem_nhdsWithin, hsmall, hlarge] with t ht htN hbig
    have hC₄le : C₄ ≤ ε / (D + 1) * t ^ (-(1 / 2 : ℝ)) := by
      rwa [div_le_iff₀' hη] at hbig
    have := hreal t ht htN.le
    nlinarith
  have hbound := chronologicalMobiusWeightedSource_norm_mellin_le hwm zero_le_one hwb hwtop
    (by positivity) hnear hρ hzero
  rw [hnormM] at hbound
  have hextra : ε / (D + 1) * D ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg (deriv riemannZeta ρ)]
  nlinarith

/-- **Cofinal lower bound at a critical zero.**  Every level `L` with `L |ζ'(ρ)| < dist(K_ρ, W)` is
exceeded by the residual of every tail in `V` at arbitrarily large `N`.  In particular, if
`ζ'(ρ) = 0` the residuals are unbounded along a subsequence, uniformly over `V`. -/
theorem chronologicalFiniteTail_cofinal_lower_bound {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ f ∈ V, ∃ K, LipschitzOnWith K f (Icc θ 1)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : riemannZeta ρ = 0) {L : ℝ} (hL : L * ‖deriv riemannZeta ρ‖ < fixedTailDefect θ V ρ) :
    ∀ N₀ : ℕ, ∃ N ≥ N₀, ∀ f ∈ V,
      L < chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) := by
  intro N₀
  by_contra hcon
  push Not at hcon
  have hle := (tailDefect_pos_and_le hθ0 hθ1 V hV hρ hzero).2 L
    (eventually_atTop.mpr ⟨N₀, fun N hN => hcon N hN⟩)
  linarith

/-- **At a multiple critical zero the residuals are unbounded along a subsequence.** -/
theorem chronologicalFiniteTail_unbounded_of_deriv_eq_zero {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ f ∈ V, ∃ K, LipschitzOnWith K f (Icc θ 1)) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    (hzero : riemannZeta ρ = 0) (hderiv : deriv riemannZeta ρ = 0) (L : ℝ) :
    ∀ N₀ : ℕ, ∃ N ≥ N₀, ∀ f ∈ V,
      L < chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) :=
  chronologicalFiniteTail_cofinal_lower_bound hθ0 hθ1 V hV hρ hzero (by
    rw [hderiv, norm_zero, mul_zero]
    exact (tailDefect_pos_and_le hθ0 hθ1 V hV hρ hzero).1)

/-- **A fixed smooth tail space cannot repair a proportional Möbius prefix.** -/
theorem chronologicalFiniteTail_obstruction {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ f ∈ V, ∃ K, LipschitzOnWith K f (Icc θ 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N ≥ N₀, ∀ f ∈ V,
      ε ≤ chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) := by
  obtain ⟨T₀, -, hT⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, -, hτ⟩ := hT T₀ le_rfl
  have hdpos := (tailDefect_pos_and_le hθ0 hθ1 V hV (linePt_re τ) hτ).1
  set d := fixedTailDefect θ V (linePt τ)
  set D := ‖deriv riemannZeta (linePt τ)‖
  have hlt : d / (D + 1) * D < d := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (deriv riemannZeta (linePt τ))]
  refine ⟨d / (D + 1), by positivity, fun N₀ => ?_⟩
  obtain ⟨N, hN, hall⟩ :=
    chronologicalFiniteTail_cofinal_lower_bound hθ0 hθ1 V hV (linePt_re τ) hτ hlt N₀
  exact ⟨N, hN, fun f hf => (hall f hf).le⟩

/-- **The obstruction for finite-dimensional subspaces of `C¹([θ, 1])`.** -/
theorem chronologicalFiniteTail_obstruction_of_contDiffOn {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (V : Submodule ℝ (ℝ → ℝ)) [FiniteDimensional ℝ V]
    (hV : ∀ f ∈ V, ContDiffOn ℝ 1 f (Icc θ 1)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N ≥ N₀, ∀ f ∈ V,
      ε ≤ chronologicalL2Norm (chronologicalHeatError (prefixTailArray θ f N) N) :=
  chronologicalFiniteTail_obstruction hθ0 hθ1 V fun f hf =>
    (hV f hf).exists_lipschitzOnWith one_ne_zero (convex_Icc θ 1) isCompact_Icc

end RHTower
