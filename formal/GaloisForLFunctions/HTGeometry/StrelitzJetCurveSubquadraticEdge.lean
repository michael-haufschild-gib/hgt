import GaloisForLFunctions.HTGeometry.StrelitzJetCurveQuadraticDecay

/-!
# Subquadratic matched Newton edges for Strelitz jet curves

The first Wiman jet is asymptotic in norm to the central index.  Therefore the selected-root
quadratic little-o estimate transfers to the first-jet scale.  A normalized branch with nonzero
limit cannot then have Newton exponent at least two.  This sharpens the exhaustive local branch
dichotomy without adding a slope premise.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- The norm of a Strelitz first jet is asymptotic to its central index. -/
theorem tendsto_strelitzRelativeNorm_div_centralIndex_one
    {ν : ℕ → ℕ} {u : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ)) :
    Tendsto (fun n => ‖u n‖ / (ν n : ℝ)) atTop (nhds 1) := by
  let E : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) * (ν n : ℝ)
  have hνpos : ∀ᶠ n : ℕ in atTop, 0 < (ν n : ℝ) := by
    have hlarge := hνTop.eventually_ge_atTop 1
    filter_upwards [hlarge] with n hn
    exact_mod_cast hn
  have hE : Tendsto (fun n => E n / (ν n : ℝ)) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine hbase.congr' ?_
    filter_upwards [hνpos] with n hn
    dsimp [E]
    field_simp
  have hratio : Tendsto (fun n => u n / (ν n : ℂ)) atTop (nhds 1) :=
    tendsto_ratio_one_of_norm_sub_le hνpos
      (Filter.Eventually.of_forall fun n => by simpa [E] using hu n) hE
  simpa [norm_div, Complex.norm_natCast] using hratio.norm

/-- Quadratic little-o relative to the central index is equivalently quadratic little-o relative
to the norm of the asymptotic first jet. -/
theorem tendsto_strelitzJetCurveRoot_div_firstJetNorm_sq_zero
    {ν : ℕ → ℕ} {u v root : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hv : ∀ n : ℕ, ‖v n‖ ≤ (1 / ((n : ℝ) + 1)) * (ν n : ℝ) ^ 2)
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    Tendsto (fun n => ‖root n‖ / ‖u n‖ ^ 2) atTop (nhds 0) := by
  have hrootν := tendsto_strelitzJetCurveRoot_div_centralIndex_sq_zero hνTop hv hclose
  have huν := tendsto_strelitzRelativeNorm_div_centralIndex_one hνTop hu
  have hquot : Tendsto (fun n =>
      (‖root n‖ / (ν n : ℝ) ^ 2) / (‖u n‖ / (ν n : ℝ)) ^ 2)
      atTop (nhds 0) := by
    have h := hrootν.div (huν.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
    change Tendsto (fun n =>
      (‖root n‖ / (ν n : ℝ) ^ 2) / (‖u n‖ / (ν n : ℝ)) ^ 2)
      atTop (nhds (0 / (1 : ℝ) ^ 2)) at h
    simpa using h
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  have huPos : ∀ᶠ n : ℕ in atTop, 0 < ‖u n‖ := huTop.eventually_gt_atTop 0
  have hνPos : ∀ᶠ n : ℕ in atTop, 0 < (ν n : ℝ) := by
    have hlarge := hνTop.eventually_ge_atTop 1
    filter_upwards [hlarge] with n hn
    exact_mod_cast hn
  refine hquot.congr' ?_
  filter_upwards [huPos, hνPos] with n hun hνn
  field_simp

/-- A nonzero normalized limit at a real-power scale cannot occur at or above a quadratic
exponent when the unnormalized values are little-o of the quadratic scale. -/
theorem lt_two_of_tendsto_div_rpow_ne_zero_of_tendsto_div_sq_zero
    {α : Type*} {l : Filter α} [l.NeBot] {b : α → ℝ} {root : α → ℂ}
    {p : ℝ} {c : ℂ} (hb : ∀ᶠ n in l, 1 ≤ b n)
    (hquad : Tendsto (fun n => ‖root n‖ / (b n) ^ 2) l (nhds 0))
    (hnormalized : Tendsto (fun n => root n / (((b n) ^ p : ℝ) : ℂ)) l (nhds c))
    (hc : c ≠ 0) : p < 2 := by
  by_contra hpnot
  have hp : (2 : ℝ) ≤ p := le_of_not_gt hpnot
  have hbound : ∀ᶠ n in l,
      ‖root n / (((b n) ^ p : ℝ) : ℂ)‖ ≤ ‖root n‖ / (b n) ^ 2 := by
    filter_upwards [hb] with n hn
    have hbpos : 0 < b n := lt_of_lt_of_le zero_lt_one hn
    have hden : (b n) ^ 2 ≤ (b n) ^ p := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hn hp
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hbpos p)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hbpos 2) hden
  have hnormZero : Tendsto (fun n => ‖root n / (((b n) ^ p : ℝ) : ℂ)‖)
      l (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) hbound hquad
  have hnormC : Tendsto (fun n => ‖root n / (((b n) ^ p : ℝ) : ℂ)‖)
      l (nhds ‖c‖) := hnormalized.norm
  have hcNorm : ‖c‖ = 0 := tendsto_nhds_unique hnormC hnormZero
  exact hc (norm_eq_zero.mp hcNorm)

/-- Complete matched Newton-edge data with the Wiman-forced strict quadratic slope ceiling. -/
def HasStrelitzJetCurveSubquadraticMatchedNewtonEdgeLimit
    (S : MvPolynomial (Fin 2) ℂ) (u root : ℕ → ℂ) : Prop :=
  ∃ i ∈ (strelitzJetCurvePolynomial S).support,
    ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
          (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
        (∀ k ∈ (strelitzJetCurvePolynomial S).support,
          strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) k ≤
            strelitzJetCurveNewtonWeight S (strelitzJetCurveNewtonSlope S i j) i) ∧
        strelitzJetCurveNewtonSlope S i j < 2 ∧
        ∃ c : ℂ, c ≠ 0 ∧
          (strelitzJetCurveNewtonEdgePolynomial S
            (strelitzJetCurveNewtonSlope S i j)
            (strelitzJetCurveNewtonWeight S
              (strelitzJetCurveNewtonSlope S i j) i)).IsRoot c ∧
          ∃ τ : ℕ → ℕ, StrictMono τ ∧
            Tendsto (fun m => strelitzJetCurveNormalizedRoot u root
              (strelitzJetCurveNewtonSlope S i j) (ns (τ m))) atTop (nhds c)

/-- The entire local Strelitz branch dichotomy, sharpened by the strict Newton-slope ceiling forced
by the second-jet Wiman estimate. -/
theorem strelitzJetCurve_subquadraticMatchedNewtonEdge_or_zeroBranch
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {ν : ℕ → ℕ} {u v root : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (hv : ∀ n : ℕ, ‖v n‖ ≤ (1 / ((n : ℝ) + 1)) * (ν n : ℝ) ^ 2)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0)) :
    HasStrelitzJetCurveSubquadraticMatchedNewtonEdgeLimit S u root ∨
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        (∀ k, root (ns k) = 0) ∧
        Tendsto (fun k => ‖v (ns k)‖) atTop (nhds 0) := by
  rcases strelitzJetCurve_matchedNewtonEdge_or_zeroBranch hS hνTop hu hroot hclose with
    hmatched | hzero
  · left
    obtain ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax,
      c, hc, hcEdge, τ, hτ, hcLim⟩ := hmatched
    have hquad :=
      tendsto_strelitzJetCurveRoot_div_firstJetNorm_sq_zero hνTop hu hv hclose
    have hcomp : StrictMono (fun m => ns (τ m)) := hns.comp hτ
    have hquadSub : Tendsto (fun m => ‖root (ns (τ m))‖ / ‖u (ns (τ m))‖ ^ 2)
        atTop (nhds 0) := hquad.comp hcomp.tendsto_atTop
    have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
      tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
    have hb : ∀ᶠ m : ℕ in atTop, 1 ≤ ‖u (ns (τ m))‖ :=
      (huTop.comp hcomp.tendsto_atTop).eventually_ge_atTop 1
    have hslopeLt : strelitzJetCurveNewtonSlope S i j < 2 :=
      lt_two_of_tendsto_div_rpow_ne_zero_of_tendsto_div_sq_zero hb hquadSub
        (by simpa [strelitzJetCurveNormalizedRoot] using hcLim) hc
    exact ⟨i, hi, j, hj, hij, ns, hns, hslope, hmax, hslopeLt,
      c, hc, hcEdge, τ, hτ, hcLim⟩
  · exact Or.inr hzero

end

end GaloisForLFunctions.HTGeometry
