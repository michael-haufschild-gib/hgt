import GaloisForLFunctions.RHTower.CCMPrimePoleCofinalWeakBoundary
import GaloisForLFunctions.RHTower.SoninCalkinNormBound

/-!
# Maximal essential alignment of finite CCM pole projections

Cofinal finite-place coherence and the intrinsic weakly-null pole boundary
produce a common approximate fixed sequence for every finite family of CCM
pole-space projections.  Compact operators vanish on this sequence.

Consequently, the average of every nonempty finite family of CCM pole
projections has essential norm exactly one, and the unnormalized sum has
essential norm exactly the number of places.  Thus finite local factors align
maximally at the essential boundary.
-/

open Filter Topology

noncomputable section

namespace RHTower

set_option maxHeartbeats 2000000 in
theorem exists_fin_ccmPrimePole_projection_common_weaklyNull_sequence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ φ : ℕ → ℕ,
      (∀ m, m < φ m) ∧
      (∀ m, ‖ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)‖ = 1) ∧
      (∀ ℓ : CCMPrimePoleHilbert →L[ℂ] ℂ,
        Tendsto (fun m => ℓ (ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)))
          atTop (𝓝 0)) ∧
      ∀ i, Tendsto (fun m =>
        ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
            (ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)) -
          ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)‖)
        atTop (𝓝 0) := by
  have hex : ∀ m : ℕ, ∃ n : ℕ, m < n ∧
      ‖ccmNormalizedPrimePoleVector Lref href n‖ = 1 ∧
      ccmNormalizedPrimePoleVector Lref href n ∈
        ccmPrimePoleClosedSubspace Lref href ∧ ∀ i,
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
          (ccmNormalizedPrimePoleVector Lref href n) -
        ccmNormalizedPrimePoleVector Lref href n‖ ^ 2 ≤
        2 * (2 * Real.pi * (((1 : ℝ) / (m + 1)) / L i)) ^ 2 := by
    intro m
    exact exists_fin_ccmPrimePole_projection_cofinal_common_coherence
      href L hL (by positivity : (0 : ℝ) < 1 / (m + 1)) m
  choose φ hφ hnorm hmem hdef using hex
  have hφtop : Tendsto φ atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    exact hm.trans (hφ m).le
  refine ⟨φ, hφ, hnorm,
    ccmNormalizedPrimePoleVector_nat_comp_weakly_tendsto_zero href φ hφtop, ?_⟩
  intro i
  have hdelta : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : Tendsto (fun m : ℕ =>
      2 * (2 * Real.pi * (((1 : ℝ) / (m + 1)) / L i)) ^ 2)
      atTop (𝓝 0) := by
    have h1 := (hdelta.div_const (L i)).const_mul (2 * Real.pi)
    have h2 := (h1.pow 2).const_mul 2
    simpa using h2
  have hsq : Tendsto (fun m =>
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
          (ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)) -
        ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)‖ ^ 2)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun m => hdef m i) hupper
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using hsqrt

set_option maxHeartbeats 2000000 in
/-- The common weakly-null boundary sequence survives every local pole-subspace measurement with
probability tending to one.  This is the Born-probability form of the simultaneous projection
defect convergence above. -/
theorem exists_fin_ccmPrimePole_projection_common_weaklyNull_born_survival_sequence
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    ∃ φ : ℕ → ℕ,
      (∀ m, m < φ m) ∧
      (∀ m, ‖ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)‖ = 1) ∧
      (∀ ℓ : CCMPrimePoleHilbert →L[ℂ] ℂ,
        Tendsto (fun m => ℓ (ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)))
          atTop (𝓝 0)) ∧
      ∀ i, Tendsto (fun m =>
        Complex.re (inner ℂ
          (ccmNormalizedPrimePoleVector Lref href (φ m : ℤ))
          ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection
            (ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)))))
        atTop (𝓝 1) := by
  obtain ⟨φ, hφ, hnorm, hweak, hproj⟩ :=
    exists_fin_ccmPrimePole_projection_common_weaklyNull_sequence href L hL
  refine ⟨φ, hφ, hnorm, hweak, fun i => ?_⟩
  let f : ℕ → CCMPrimePoleHilbert := fun m =>
    ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)
  have hnorm_f : ∀ m, ‖f m‖ = 1 := hnorm
  have hproj_i : Tendsto (fun m =>
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m‖)
      atTop (𝓝 0) := hproj i
  have hsq := hproj_i.pow 2
  norm_num at hsq
  have hsq' : Tendsto (fun m =>
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m‖ ^ 2)
      atTop (𝓝 0) := hsq
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub' : Tendsto (fun m =>
      (1 : ℝ) -
        ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m‖ ^ 2)
      atTop (𝓝 (1 - 0)) := hone.sub hsq'
  norm_num at hsub'
  refine hsub'.congr' (Eventually.of_forall fun m => ?_)
  change (1 -
      ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m‖ ^ 2) =
    Complex.re (inner ℂ (f m)
      ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m)))
  exact (HTGeometry.bornSurvivalProbability_eq_one_sub_projectionDefectSq
    (k := ℂ) (E := CCMPrimePoleHilbert)
    (ccmPrimePoleClosedSubspace (L i) (hL i)) (f m) (hnorm_f m)).symm

def ccmPrimePoleProjectionAverage
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert :=
  ((d : ℂ)⁻¹) • ∑ i,
    (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection

theorem norm_ccmPrimePoleProjectionAverage_le_one
    {d : ℕ} (hd : 0 < d) (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    ‖ccmPrimePoleProjectionAverage L hL‖ ≤ 1 := by
  have hsum :
      ‖∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection‖ ≤ d := by
    calc
      ‖∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection‖ ≤
          ∑ i, ‖(ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
        gcongr with i
        exact Submodule.starProjection_norm_le _
      _ = d := by simp
  calc
    ‖ccmPrimePoleProjectionAverage L hL‖ ≤
        ‖((d : ℂ)⁻¹)‖ *
          ‖∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection‖ :=
      by
        change ‖((d : ℂ)⁻¹) •
          ∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection‖ ≤ _
        exact norm_smul_le ((d : ℂ)⁻¹)
          (∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection)
    _ ≤ ‖((d : ℂ)⁻¹)‖ * d :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 1 := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp

theorem essentialNorm_ccmPrimePoleProjectionAverage
    {d : ℕ} (hd : 0 < d) {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    essentialNorm (ccmPrimePoleProjectionAverage L hL) = 1 := by
  obtain ⟨φ, hφ, hnorm, hweak, hproj⟩ :=
    exists_fin_ccmPrimePole_projection_common_weaklyNull_sequence href L hL
  let f : ℕ → CCMPrimePoleHilbert := fun m =>
    ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)
  have hprojVec : ∀ i, Tendsto (fun m =>
      (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m)
      atTop (𝓝 0) := by
    intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [f] using hproj i
  have hsumVec : Tendsto (fun m => ∑ i,
      ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hprojVec i)
  have havgVec : Tendsto (fun m =>
      ((d : ℂ)⁻¹) • ∑ i,
        ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m))
      atTop (𝓝 0) := by
    simpa using hsumVec.const_smul ((d : ℂ)⁻¹)
  have hpoint (m : ℕ) :
      ccmPrimePoleProjectionAverage L hL (f m) - f m =
        ((d : ℂ)⁻¹) • ∑ i,
          ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m) := by
    have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    simp only [ccmPrimePoleProjectionAverage, _root_.smul_apply,
      _root_.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
      smul_sub]
    rw [Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ d (f m)]
    exact congrArg
      (fun x : CCMPrimePoleHilbert =>
        ((d : ℂ)⁻¹) • ∑ i,
          (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - x)
      (inv_smul_smul₀ hdC (f m)).symm
  have hTvec : Tendsto (fun m =>
      ccmPrimePoleProjectionAverage L hL (f m) - f m) atTop (𝓝 0) := by
    simpa only [hpoint] using havgVec
  have hTnorm : Tendsto (fun m =>
      ‖ccmPrimePoleProjectionAverage L hL (f m) - f m‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hTvec
  apply le_antisymm
  · exact (essentialNorm_le _ 0 isCompactOperator_zero).trans (by
      simpa using norm_ccmPrimePoleProjectionAverage_le_one hd L hL)
  · apply le_essentialNorm
    intro K hK
    apply one_le_norm_sub_compact_of_approx
      (ccmPrimePoleProjectionAverage L hL) f f
    · intro m
      rw [hnorm m]
    · simpa only [f] using hweak
    · exact hnorm
    · exact hTnorm
    · exact hK

theorem essentialNorm_sum_ccmPrimePoleProjections
    {d : ℕ} (hd : 0 < d) {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    essentialNorm
      (∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection) = d := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hop :
      (∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection) =
        (d : ℂ) • ccmPrimePoleProjectionAverage L hL := by
    rw [ccmPrimePoleProjectionAverage, smul_smul, mul_inv_cancel₀ hdC, one_smul]
  rw [hop, essentialNorm_smul,
    essentialNorm_ccmPrimePoleProjectionAverage hd href L hL,
    Complex.norm_natCast, mul_one]

/-- Headline boundary law without a separately supplied reference scale: the
essential norm of a nonempty finite sum is exactly its cardinality. -/
theorem essentialNorm_sum_ccmPrimePoleProjections_eq_card
    {d : ℕ} (hd : 0 < d) (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) :
    essentialNorm
      (∑ i, (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection) = d :=
  essentialNorm_sum_ccmPrimePoleProjections hd (hL ⟨0, hd⟩) L hL

/-- Prime-local specialization of maximal essential alignment. -/
theorem essentialNorm_sum_prime_ccmPrimePoleProjections_eq_card
    {d : ℕ} (hd : 0 < d) (p : Fin d → ℕ) (hp : ∀ i, (p i).Prime) :
    essentialNorm
      (∑ i, (ccmPrimePoleClosedSubspace (Real.log (p i))
        (Real.log_pos (by exact_mod_cast (hp i).one_lt))).starProjection) = d := by
  exact essentialNorm_sum_ccmPrimePoleProjections_eq_card hd
    (fun i => Real.log (p i))
    (fun i => Real.log_pos (by exact_mod_cast (hp i).one_lt))

/-- A finite nonnegative linear combination of CCM pole projections. -/
def ccmPrimePoleProjectionPositiveCombination
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i) (a : Fin d → ℝ) :
    CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert :=
  ∑ i, (a i : ℂ) •
    (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection

theorem norm_ccmPrimePoleProjectionPositiveCombination_le
    {d : ℕ} (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ‖ccmPrimePoleProjectionPositiveCombination L hL a‖ ≤ ∑ i, a i := by
  calc
    ‖ccmPrimePoleProjectionPositiveCombination L hL a‖ ≤
        ∑ i, ‖(a i : ℂ) •
          (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, a i := by
      gcongr with i
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i)]
      exact mul_le_of_le_one_right (ha i) (Submodule.starProjection_norm_le _)

/-- Strongest positive-cone form of maximal essential alignment: every
nonnegative finite combination has essential norm equal to the sum of its
weights. -/
theorem essentialNorm_ccmPrimePoleProjectionPositiveCombination
    {d : ℕ} {Lref : ℝ} (href : 0 < Lref)
    (L : Fin d → ℝ) (hL : ∀ i, 0 < L i)
    (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) :
    essentialNorm (ccmPrimePoleProjectionPositiveCombination L hL a) = ∑ i, a i := by
  let c : ℝ := ∑ i, a i
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => ha i
  rcases hc.eq_or_lt with hc0 | hcpos
  · have hsum0 : ∑ i, a i = 0 := by simpa [c] using hc0.symm
    have hai : ∀ i, a i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ha j).mp hsum0 i
        (Finset.mem_univ i)
    have hop : ccmPrimePoleProjectionPositiveCombination L hL a = 0 := by
      rw [ccmPrimePoleProjectionPositiveCombination]
      apply Finset.sum_eq_zero
      intro i hi
      rw [hai i, Complex.ofReal_zero, zero_smul]
    rw [hop, essentialNorm_zero, hsum0]
  obtain ⟨φ, hφ, hnorm, hweak, hproj⟩ :=
    exists_fin_ccmPrimePole_projection_common_weaklyNull_sequence href L hL
  let f : ℕ → CCMPrimePoleHilbert := fun m =>
    ccmNormalizedPrimePoleVector Lref href (φ m : ℤ)
  have hprojVec : ∀ i, Tendsto (fun m =>
      (ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m)
      atTop (𝓝 0) := by
    intro i
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [f] using hproj i
  have hweighted : Tendsto (fun m => ∑ i,
      (a i : ℂ) •
        ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m))
      atTop (𝓝 0) := by
    simpa only [smul_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ
        (fun i _ => (hprojVec i).const_smul (a i : ℂ))
  have hpoint (m : ℕ) :
      ccmPrimePoleProjectionPositiveCombination L hL a (f m) - (c : ℂ) • f m =
        ∑ i, (a i : ℂ) •
          ((ccmPrimePoleClosedSubspace (L i) (hL i)).starProjection (f m) - f m) := by
    simp only [ccmPrimePoleProjectionPositiveCombination, _root_.sum_apply,
      _root_.smul_apply, smul_sub, Finset.sum_sub_distrib]
    have hcCsum : (c : ℂ) = ∑ i, (a i : ℂ) := by simp [c]
    rw [hcCsum, Finset.sum_smul]
  have hTvec : Tendsto (fun m =>
      ccmPrimePoleProjectionPositiveCombination L hL a (f m) - (c : ℂ) • f m)
      atTop (𝓝 0) := by
    simpa only [hpoint] using hweighted
  let T₁ : CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert :=
    (c : ℂ)⁻¹ • ccmPrimePoleProjectionPositiveCombination L hL a
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hT₁point (m : ℕ) : T₁ (f m) - f m =
      (c : ℂ)⁻¹ •
        (ccmPrimePoleProjectionPositiveCombination L hL a (f m) - (c : ℂ) • f m) := by
    dsimp [T₁]
    rw [smul_sub]
    exact congrArg
      (fun x : CCMPrimePoleHilbert =>
        (c : ℂ)⁻¹ • ccmPrimePoleProjectionPositiveCombination L hL a (f m) - x)
      (inv_smul_smul₀ hcC (f m)).symm
  have hT₁vec : Tendsto (fun m => T₁ (f m) - f m) atTop (𝓝 0) := by
    have h := hTvec.const_smul ((c : ℂ)⁻¹)
    simpa only [hT₁point, smul_zero] using h
  have hT₁norm : Tendsto (fun m => ‖T₁ (f m) - f m‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hT₁vec
  have hdist : ∀ K : CCMPrimePoleHilbert →L[ℂ] CCMPrimePoleHilbert,
      IsCompactOperator K → 1 ≤ ‖T₁ - K‖ := by
    intro K hK
    exact one_le_norm_sub_compact_of_approx T₁ f f
      (fun m => by rw [hnorm m]) (by simpa only [f] using hweak) hnorm hT₁norm K hK
  apply le_antisymm
  · exact (essentialNorm_le _ 0 isCompactOperator_zero).trans (by
      simpa using norm_ccmPrimePoleProjectionPositiveCombination_le L hL a ha)
  · apply le_essentialNorm
    intro K hK
    have hlower := norm_smul_le_norm_smul_sub_compact_of_one_le
      (c : ℂ) hcC T₁ K hdist hK
    have hscale : (c : ℂ) • T₁ = ccmPrimePoleProjectionPositiveCombination L hL a := by
      dsimp [T₁]
      change (c : ℂ) • ((c : ℂ)⁻¹ • ccmPrimePoleProjectionPositiveCombination L hL a) = _
      rw [smul_smul, mul_inv_cancel₀ hcC, one_smul]
    rw [hscale, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos] at hlower
    exact hlower

end RHTower
