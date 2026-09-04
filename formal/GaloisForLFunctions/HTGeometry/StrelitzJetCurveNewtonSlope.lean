import GaloisForLFunctions.HTGeometry.StrelitzJetCurveReciprocalGrowth
import GaloisForLFunctions.HTGeometry.NewtonEdgeNonCancellation

/-!
# Newton slopes of numerical Strelitz jet-curve branches

Two-sided polynomial bounds confine every nonzero branch's logarithmic slope to a compact interval.
After subsequence extraction, the corpus log-scale noncancellation theorem forces the maximal
Newton weight of the fixed curve to occur at least twice.  The limit is therefore one of the finite
rational slopes determined by two distinct curve monomials.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Logarithmic growth slope of a numerical branch relative to its escaping base variable. -/
def strelitzJetCurveRootLogSlope (u root : ℕ → ℂ) (n : ℕ) : ℝ :=
  Real.log ‖root n‖ / Real.log ‖u n‖

/-- Two-sided polynomial bounds put a nonzero value's logarithmic slope in a fixed compact
interval once the base exceeds both constants. -/
theorem strelitzJetCurveRootLogSlope_mem_Icc
    {u root : ℕ → ℂ} {n D : ℕ} {C₀ C₁ : ℝ}
    (hroot : root n ≠ 0) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hbase : max (C₀ * 2 ^ D) (C₁ * 2 ^ D) ≤ ‖u n‖)
    (hbase1 : 1 < ‖u n‖)
    (hupper : ‖root n‖ ≤ C₁ * (1 + ‖u n‖) ^ D)
    (hlower : ‖(root n)⁻¹‖ ≤ C₀ * (1 + ‖u n‖) ^ D) :
    strelitzJetCurveRootLogSlope u root n ∈
      Set.Icc (-((D : ℝ) + 1)) ((D : ℝ) + 1) := by
  let ρ : ℝ := ‖u n‖
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos (by simpa [ρ] using hbase1)
  have hC₀' : C₀ * 2 ^ D ≤ ρ :=
    le_trans (le_max_left _ _) (by simpa [ρ] using hbase)
  have hC₁' : C₁ * 2 ^ D ≤ ρ :=
    le_trans (le_max_right _ _) (by simpa [ρ] using hbase)
  have honeadd : 1 + ρ ≤ 2 * ρ := by linarith
  have hpow : ρ * ρ ^ D = ρ ^ (D + 1) := by rw [pow_succ']
  have hupperPow : ‖root n‖ ≤ ρ ^ (D + 1) := by
    calc
      ‖root n‖ ≤ C₁ * (1 + ρ) ^ D := by simpa [ρ] using hupper
      _ ≤ C₁ * (2 * ρ) ^ D :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) honeadd D) hC₁
      _ = (C₁ * 2 ^ D) * ρ ^ D := by rw [mul_pow]; ring
      _ ≤ ρ * ρ ^ D := mul_le_mul_of_nonneg_right hC₁' (by positivity)
      _ = ρ ^ (D + 1) := hpow
  have hlowerPow : ‖(root n)⁻¹‖ ≤ ρ ^ (D + 1) := by
    calc
      ‖(root n)⁻¹‖ ≤ C₀ * (1 + ρ) ^ D := by simpa [ρ] using hlower
      _ ≤ C₀ * (2 * ρ) ^ D :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) honeadd D) hC₀
      _ = (C₀ * 2 ^ D) * ρ ^ D := by rw [mul_pow]; ring
      _ ≤ ρ * ρ ^ D := mul_le_mul_of_nonneg_right hC₀' (by positivity)
      _ = ρ ^ (D + 1) := hpow
  have hnormpos : 0 < ‖root n‖ := norm_pos_iff.mpr hroot
  have hlogUpper : Real.log ‖root n‖ ≤ ((D : ℝ) + 1) * Real.log ρ := by
    calc
      Real.log ‖root n‖ ≤ Real.log (ρ ^ (D + 1)) :=
        Real.log_le_log hnormpos hupperPow
      _ = ((D : ℝ) + 1) * Real.log ρ := by
        rw [Real.log_pow]
        push_cast
        rfl
  have hlogLower : -(((D : ℝ) + 1) * Real.log ρ) ≤ Real.log ‖root n‖ := by
    have hinvpos : 0 < ‖(root n)⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hroot)
    have h := Real.log_le_log hinvpos hlowerPow
    rw [norm_inv, Real.log_inv, Real.log_pow] at h
    push_cast at h
    linarith
  constructor
  · rw [strelitzJetCurveRootLogSlope]
    change -((D : ℝ) + 1) ≤ Real.log ‖root n‖ / Real.log ρ
    rw [le_div_iff₀ hlogρ]
    linarith
  · rw [strelitzJetCurveRootLogSlope]
    change Real.log ‖root n‖ / Real.log ρ ≤ (D : ℝ) + 1
    rw [div_le_iff₀ hlogρ]
    exact hlogUpper

/-- Every eventually nonzero specialized root has its logarithmic slope eventually confined to one
fixed compact interval. -/
theorem eventually_strelitzJetCurveRootLogSlope_mem_Icc
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0) :
    ∀ᶠ n : ℕ in atTop, strelitzJetCurveRootLogSlope u root n ∈
      Set.Icc (-((strelitzJetCurveCoefficientDegree S : ℝ) + 1))
        ((strelitzJetCurveCoefficientDegree S : ℝ) + 1) := by
  obtain ⟨C₁, hC₁, hupper⟩ :=
    exists_eventually_norm_root_le_strelitzJetCurvePolynomialGrowth hS huTop hroot
  obtain ⟨C₀, hC₀, hlower⟩ :=
    exists_eventually_norm_inv_root_le_strelitzJetCurvePolynomialGrowth
      hS huTop hroot hroot0
  have hlarge := huTop.eventually_ge_atTop (max
    (C₀ * 2 ^ strelitzJetCurveCoefficientDegree S)
    (C₁ * 2 ^ strelitzJetCurveCoefficientDegree S))
  have hpos := huTop.eventually_gt_atTop 1
  filter_upwards [hroot0, hupper, hlower, hlarge, hpos] with n hn0 hnupper hnlower hnlarge hnpos
  apply strelitzJetCurveRootLogSlope_mem_Icc hn0 hC₀.le hC₁.le
  · exact hnlarge
  · exact hnpos
  · exact hnupper
  · exact hnlower

/-- A nonzero numerical branch of the fixed algebraic jet curve has a finite limiting logarithmic
slope after passage to a cofinal subsequence. -/
theorem exists_strelitzJetCurveRootLogSlope_tendsto_subsequence
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0) :
    ∃ p ∈ Set.Icc (-((strelitzJetCurveCoefficientDegree S : ℝ) + 1))
        ((strelitzJetCurveCoefficientDegree S : ℝ) + 1),
      ∃ ns : ℕ → ℕ, StrictMono ns ∧
        Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop (nhds p) := by
  let a : ℝ := -((strelitzJetCurveCoefficientDegree S : ℝ) + 1)
  let b : ℝ := (strelitzJetCurveCoefficientDegree S : ℝ) + 1
  let clipped : ℕ → ℝ := fun n => max a (min b (strelitzJetCurveRootLogSlope u root n))
  have hab : a ≤ b := by
    have hd : 0 ≤ (strelitzJetCurveCoefficientDegree S : ℝ) := by positivity
    dsimp [a, b]
    linarith
  have hclip : ∀ n, clipped n ∈ Set.Icc a b := by
    intro n
    constructor
    · exact le_max_left _ _
    · exact max_le hab (min_le_left _ _)
  obtain ⟨p, hp, ns, hns, hlim⟩ := isCompact_Icc.tendsto_subseq hclip
  have hevent := eventually_strelitzJetCurveRootLogSlope_mem_Icc hS huTop hroot hroot0
  have heventSub : ∀ᶠ k : ℕ in atTop,
      strelitzJetCurveRootLogSlope u root (ns k) ∈ Set.Icc a b := by
    have hsub := hns.tendsto_atTop.eventually hevent
    simpa only [Set.mem_Icc, a, b] using hsub
  have heq : ∀ᶠ k : ℕ in atTop,
      clipped (ns k) = strelitzJetCurveRootLogSlope u root (ns k) := by
    filter_upwards [heventSub] with k hk
    simp [clipped, hk.1, hk.2]
  refine ⟨p, by simpa [a, b] using hp, ns, hns, ?_⟩
  refine Tendsto.congr' ?_ hlim
  filter_upwards [heq] with k hk
  simpa [Function.comp_def] using hk

/-- Any complex family escaping in norm has exponent one when measured against its own norm. -/
theorem hasLogScaleExponent_self_norm
    {u : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) :
    HasLogScaleExponent atTop (fun n => ‖u n‖) u 1 := by
  constructor
  · have hpos := huTop.eventually_gt_atTop 0
    filter_upwards [hpos] with n hn
    exact norm_pos_iff.mp hn
  · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
    have hlarge := huTop.eventually_gt_atTop 1
    filter_upwards [hlarge] with n hn
    exact (div_self (ne_of_gt (Real.log_pos hn))).symm

/-- A limiting logarithmic slope of exact specialized roots is a genuine Newton slope: the maximal
weight among the fixed curve's nonzero monomials is attained at least twice. -/
theorem exists_distinct_strelitzJetCurveNewtonWeight_eq
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} {p : ℝ} {ns : ℕ → ℕ} (hns : StrictMono ns)
    (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0)
    (hslope : Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k))
      atTop (nhds p)) :
    ∃ i ∈ (strelitzJetCurvePolynomial S).support,
      ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
        ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff i)).natDegree : ℝ) +
            (i : ℝ) * p =
          ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j)).natDegree : ℝ) +
            (j : ℝ) * p ∧
        ∀ k ∈ (strelitzJetCurvePolynomial S).support,
          ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)).natDegree : ℝ) +
              (k : ℝ) * p ≤
            ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff i)).natDegree : ℝ) +
              (i : ℝ) * p := by
  classical
  let R := strelitzJetCurvePolynomial S
  let q : ℕ → Polynomial ℂ := fun i => finOnePolynomial (R.coeff i)
  let w : ℕ → ℝ := fun i => (q i).natDegree + (i : ℝ) * p
  have hR : R ≠ 0 := strelitzJetCurvePolynomial_ne_zero hS
  have hsupport : R.support.Nonempty := Polynomial.support_nonempty.mpr hR
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image R.support w hsupport
  have huTopSub : Tendsto (fun k => ‖u (ns k)‖) atTop atTop :=
    huTop.comp hns.tendsto_atTop
  have hu : HasLogScaleExponent atTop (fun k => ‖u (ns k)‖) (fun k => u (ns k)) 1 :=
    hasLogScaleExponent_self_norm huTopSub
  have hroot0Sub : ∀ᶠ k : ℕ in atTop, root (ns k) ≠ 0 :=
    hns.tendsto_atTop.eventually hroot0
  have hT : HasLogScaleExponent atTop (fun k => ‖u (ns k)‖) (fun k => root (ns k)) p := by
    refine ⟨hroot0Sub, ?_⟩
    simpa [strelitzJetCurveRootLogSlope] using hslope
  have hq : ∀ i ∈ R.support, q i ≠ 0 := by
    intro i hi
    exact finOnePolynomial_ne_zero (Polynomial.mem_support_iff.mp hi)
  have hsum : ∀ᶠ k : ℕ in atTop,
      ∑ i ∈ R.support, (q i).eval (u (ns k)) * (root (ns k)) ^ i = 0 := by
    have hrootSub := hns.tendsto_atTop.eventually hroot
    filter_upwards [hrootSub] with k hk
    have hk' : (strelitzJetCurveSpecialization S (u (ns k))).eval (root (ns k)) = 0 := hk
    rw [strelitzJetCurveSpecialization, Polynomial.eval_map,
      Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hk'
    simpa [R, q, eval_finOnePolynomial] using hk'
  obtain ⟨j, hj, hji, hweight⟩ : ∃ j ∈ R.support, j ≠ i₀ ∧ w j = w i₀ := by
    by_contra hnone
    push Not at hnone
    have hstrict : ∀ i ∈ R.support, i ≠ i₀ → w i < w i₀ := by
      intro i hi hne
      exact lt_of_le_of_ne (hmax i hi) (hnone i hi hne)
    exact (not_eventually_newton_sum_eq_zero_of_unique_max huTopSub hu hT
      R.support q id hi₀ hq (by simpa [w] using hstrict)) hsum
  refine ⟨i₀, hi₀, j, hj, hji.symm, ?_, ?_⟩
  · simpa [w, q, R] using hweight.symm
  · intro k hk
    simpa [w, q, R] using hmax k hk

/-- Rational Newton slope determined by two distinct monomials of the fixed jet curve. -/
def strelitzJetCurveNewtonSlope (S : MvPolynomial (Fin 2) ℂ) (i j : ℕ) : ℝ :=
  (((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j)).natDegree : ℝ) -
      ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff i)).natDegree : ℝ)) /
    ((i : ℝ) - (j : ℝ))

theorem eq_strelitzJetCurveNewtonSlope_of_weight_eq
    (S : MvPolynomial (Fin 2) ℂ) {p : ℝ} {i j : ℕ} (hij : i ≠ j)
    (hweight :
      ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff i)).natDegree : ℝ) +
          (i : ℝ) * p =
        ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff j)).natDegree : ℝ) +
          (j : ℝ) * p) :
    p = strelitzJetCurveNewtonSlope S i j := by
  have hden : (i : ℝ) - (j : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hij)
  rw [strelitzJetCurveNewtonSlope, eq_div_iff hden]
  linarith

/-- **Finite Newton-slope extraction.**  Every eventually nonzero root sequence of a fixed
Strelitz jet curve, over an escaping base sequence, has a cofinal subsequence whose logarithmic
slope converges to the rational slope of two distinct monomials on one maximal Newton face. -/
theorem exists_strelitzJetCurveNewtonSlope_tendsto_subsequence
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u root : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n))
    (hroot0 : ∀ᶠ n : ℕ in atTop, root n ≠ 0) :
    ∃ i ∈ (strelitzJetCurvePolynomial S).support,
      ∃ j ∈ (strelitzJetCurvePolynomial S).support, i ≠ j ∧
        ∃ ns : ℕ → ℕ, StrictMono ns ∧
          Tendsto (fun k => strelitzJetCurveRootLogSlope u root (ns k)) atTop
            (nhds (strelitzJetCurveNewtonSlope S i j)) ∧
          ∀ k ∈ (strelitzJetCurvePolynomial S).support,
            ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)).natDegree : ℝ) +
                (k : ℝ) * strelitzJetCurveNewtonSlope S i j ≤
              ((finOnePolynomial ((strelitzJetCurvePolynomial S).coeff i)).natDegree : ℝ) +
                (i : ℝ) * strelitzJetCurveNewtonSlope S i j := by
  obtain ⟨p, hp, ns, hns, hslope⟩ :=
    exists_strelitzJetCurveRootLogSlope_tendsto_subsequence hS huTop hroot hroot0
  obtain ⟨i, hi, j, hj, hij, hweight, hmax⟩ :=
    exists_distinct_strelitzJetCurveNewtonWeight_eq hS hns huTop hroot hroot0 hslope
  have hpSlope : p = strelitzJetCurveNewtonSlope S i j :=
    eq_strelitzJetCurveNewtonSlope_of_weight_eq S hij hweight
  refine ⟨i, hi, j, hj, hij, ns, hns, ?_, ?_⟩
  · simpa [hpSlope] using hslope
  · intro k hk
    simpa [hpSlope] using hmax k hk

end

end GaloisForLFunctions.HTGeometry
