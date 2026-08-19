import GaloisForLFunctions.HTGeometry.QuasiAbelianComplementGrowthData

/-!
# The seed bound on an arbitrary compact set

The damped bound holds only on a region small compared with the lattice spacing, because that is
what makes the damping rate positive.  Local normal convergence of the Poincaré series, by contrast,
is a statement at a **fixed** scale on **every** compact set, so it needs no damping at all: the
constant may depend on the compact set and on the scale.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A compact set has a uniform radius about any centre. -/
theorem exists_centered_radius_of_isCompact {d : ℕ} (center : Fin d → ℂ)
    {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x ∈ K, ∀ i,
      |(x i).re - (center i).re| ≤ ρ ∧ |(x i).im - (center i).im| ≤ ρ := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  refine ⟨R + ∑ j, (|(center j).re| + |(center j).im|), by positivity, fun x hx i => ?_⟩
  have hxi := hR x hx i
  have hcj : |(center i).re| + |(center i).im|
      ≤ ∑ j, (|(center j).re| + |(center j).im|) :=
    Finset.single_le_sum (f := fun j => |(center j).re| + |(center j).im|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  constructor
  · have h1 : |(x i).re - (center i).re| ≤ |(x i).re| + |(center i).re| := abs_sub _ _
    have := abs_nonneg ((center i).im)
    linarith [hxi.1]
  · have h1 : |(x i).im - (center i).im| ≤ |(x i).im| + |(center i).im| := abs_sub _ _
    have := abs_nonneg ((center i).re)
    linarith [hxi.2]

/-- **The scaled Gaussian on an arbitrary compact set.**  No smallness hypothesis: the constant
absorbs the region. -/
theorem exists_norm_scaledGaussian_realTranslate_le {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (center : Fin d → ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin d → ℝ) (x : Fin d → ℂ), x ∈ K →
      ‖(centeredComplexGaussian (fun i => B * σ i) center).1 (x + fun i => ((v i : ℝ) : ℂ))‖
        ≤ C * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2) := by
  classical
  obtain ⟨ρ, hρ0, hρ⟩ := exists_centered_radius_of_isCompact center hK
  have hB0 : (0 : ℝ) < B := by linarith
  refine ⟨Real.exp (B * ((∑ i, σ i) * (2 * ρ ^ 2))), (Real.exp_pos _).le, fun v x hx => ?_⟩
  rw [norm_centeredComplexGaussian_apply, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hterm : ∀ i : Fin d,
      -((B * σ i) * ((((x + fun j => ((v j : ℝ) : ℂ)) i - center i).re) ^ 2
          - (((x + fun j => ((v j : ℝ) : ℂ)) i - center i).im) ^ 2))
        ≤ B * (σ i * (2 * ρ ^ 2)) - σ i / 4 * (v i) ^ 2 := by
    intro i
    have hre : (((x + fun j => ((v j : ℝ) : ℂ)) i - center i)).re
        = (x i).re + v i - (center i).re := by
      simp [Complex.add_re, Complex.sub_re]
    have him : (((x + fun j => ((v j : ℝ) : ℂ)) i - center i)).im
        = (x i).im - (center i).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [hre, him]
    obtain ⟨ht, hu⟩ := hρ x hx i
    set t : ℝ := (x i).re - (center i).re with htdef
    set u : ℝ := (x i).im - (center i).im with hudef
    have hsum : (x i).re + v i - (center i).re = v i + t := by rw [htdef]; ring
    rw [hsum]
    have ht2 : t ^ 2 ≤ ρ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
      rwa [sq_abs] at h
    have hu2 : u ^ 2 ≤ ρ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
      rwa [sq_abs] at h
    have hkey : (v i) ^ 2 / 2 - t ^ 2 ≤ (v i + t) ^ 2 := by
      nlinarith [sq_nonneg (v i + 2 * t)]
    have hσi := (hσ i).le
    have hBσ : (0 : ℝ) ≤ B * σ i := mul_nonneg hB0.le hσi
    have hshrink : σ i / 4 * (v i) ^ 2 ≤ B * σ i * ((v i) ^ 2 / 2) := by
      have hprod : (0 : ℝ) ≤ (B - 1) * σ i * (v i) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) hσi) (sq_nonneg _)
      nlinarith [sq_nonneg (v i), hσi, hprod]
    nlinarith [mul_le_mul_of_nonneg_left hkey hBσ,
      mul_le_mul_of_nonneg_left ht2 hBσ, mul_le_mul_of_nonneg_left hu2 hBσ, hshrink]
  have hsum_le : (-∑ i, (B * σ i) * ((((x + fun j => ((v j : ℝ) : ℂ)) i - center i).re) ^ 2
        - (((x + fun j => ((v j : ℝ) : ℂ)) i - center i).im) ^ 2))
      ≤ ∑ i, (B * (σ i * (2 * ρ ^ 2)) - σ i / 4 * (v i) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  refine le_trans hsum_le ?_
  rw [Finset.sum_sub_distrib]
  have hA : ∑ i, B * (σ i * (2 * ρ ^ 2)) = B * ((∑ i, σ i) * (2 * ρ ^ 2)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hA]
  linarith

set_option maxHeartbeats 1000000 in
/-- **The damped seed on an arbitrary compact set.**  At a fixed scale the constant may depend on
the compact set and on the scale, so no smallness hypothesis is needed; this is what local normal
convergence of the Poincaré series consumes. -/
theorem exists_norm_dampedFlatSeed_realTranslate_le {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (w : I → Fin d → ℂ) (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w)
    (target : I) {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (P : MvPolynomial (Fin d) ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin d → ℝ) (x : Fin d → ℂ), x ∈ K →
      ‖(dampedFlatSeed w hdistinct target hm σ P B).1 (x + fun i => ((v i : ℝ) : ℂ))‖
        ≤ C * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2)) := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  obtain ⟨Cb, hCb0, hCb⟩ :=
    (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump_stripBounded R
  obtain ⟨Cp, hCp0, hCp⟩ := exists_norm_mvPolynomial_eval_le P
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_scaledGaussian_realTranslate_le σ hσ (w target) hK hB
  have hgs0 : (0 : ℝ) ≤ ∑ r ∈ Finset.range m, (1 + C₀) ^ r :=
    Finset.sum_nonneg fun r _ => pow_nonneg (by linarith) r
  have hprodR0 : (0 : ℝ) ≤ ∏ i, (1 + 2 * R) ^ (P.degreeOf i) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (by linarith) _
  refine ⟨Cb * ((C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
    * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i))),
    mul_nonneg hCb0 (mul_nonneg (mul_nonneg hC₀0 hgs0) (mul_nonneg hCp0 hprodR0)),
    fun v x hx => ?_⟩
  set y : Fin d → ℂ := x + fun i => ((v i : ℝ) : ℂ) with hy
  set G : ℂ := (centeredComplexGaussian (fun i => B * σ i) (w target)).1 y with hGdef
  have hGb : ‖G‖ ≤ C₀ * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2) := hC₀ v x hx
  have hexp2 : Real.exp (-∑ i, σ i / 4 * (v i) ^ 2) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : (0 : ℝ) ≤ ∑ i, σ i / 4 * (v i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by linarith [hσ i]) (sq_nonneg _)
    linarith
  have hGle : ‖G‖ ≤ C₀ := by
    refine le_trans hGb ?_
    nlinarith [hexp2, hC₀0, (Real.exp_pos (-∑ i, σ i / 4 * (v i) ^ 2)).le]
  have hgeom : ∑ r ∈ Finset.range m, (1 + ‖G‖) ^ r
      ≤ ∑ r ∈ Finset.range m, (1 + C₀) ^ r :=
    Finset.sum_le_sum fun r _ =>
      pow_le_pow_left₀ (by positivity) (by linarith) r
  have hdamp : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
      ≤ ‖G‖ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r :=
    le_trans (norm_damping_le (fun i => B * σ i) (w target) hm _)
      (mul_le_mul_of_nonneg_left hgeom (norm_nonneg _))
  have hstrip : ∀ c : Fin d, |(y c).im| ≤ R := by
    intro c
    have him : (y c).im = (x c).im := by simp [hy, Complex.add_im]
    rw [him]
    exact (hR x hx c).2
  have h1 := hCb y hstrip
  have hcoord : ∀ i : Fin d, 1 + ‖y i‖ ≤ (1 + 2 * R) * (1 + |v i|) := by
    intro i
    have hxi := hR x hx i
    have hxnorm : ‖x i‖ ≤ 2 * R := by
      have := Complex.norm_le_abs_re_add_abs_im (x i)
      linarith [hxi.1, hxi.2]
    have hyi : ‖y i‖ ≤ ‖x i‖ + |v i| := by
      have hval : y i = x i + ((v i : ℝ) : ℂ) := by simp [hy]
      rw [hval]
      refine le_trans (norm_add_le _ _) ?_
      simp
    nlinarith [abs_nonneg (v i), norm_nonneg (x i), hR0]
  have h3 : ‖MvPolynomial.eval y P‖
      ≤ (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i) := by
    refine le_trans (hCp y) ?_
    have hprod : ∏ i, (1 + ‖y i‖) ^ (P.degreeOf i)
        ≤ ∏ i, ((1 + 2 * R) * (1 + |v i|)) ^ (P.degreeOf i) :=
      Finset.prod_le_prod (fun i _ => by positivity)
        (fun i _ => pow_le_pow_left₀ (by positivity) (hcoord i) _)
    have hsplit : ∏ i, ((1 + 2 * R) * (1 + |v i|)) ^ (P.degreeOf i)
        = (∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [mul_pow]
    calc Cp * ∏ i, (1 + ‖y i‖) ^ (P.degreeOf i)
        ≤ Cp * ∏ i, ((1 + 2 * R) * (1 + |v i|)) ^ (P.degreeOf i) :=
          mul_le_mul_of_nonneg_left hprod hCp0
      _ = (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i) := by
          rw [hsplit]; ring
  have hval : (dampedFlatSeed w hdistinct target hm σ P B).1 y
      = (flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1 y
        * ((gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y
          * MvPolynomial.eval y P) := rfl
  rw [hval, norm_mul, norm_mul]
  have hstep : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
        * ‖MvPolynomial.eval y P‖
      ≤ ((C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
          * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
        * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2)) := by
    have hd1 : ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
        ≤ (C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
          * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2) := by
      refine le_trans hdamp ?_
      nlinarith [hGb, norm_nonneg G, hgs0]
    calc ‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
          * ‖MvPolynomial.eval y P‖
        ≤ ((C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
            * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2))
          * ((Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)) * ∏ i, (1 + |v i|) ^ (P.degreeOf i)) :=
          mul_le_mul hd1 h3 (norm_nonneg _)
            (mul_nonneg (mul_nonneg hC₀0 hgs0) (Real.exp_pos _).le)
      _ = ((C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
            * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
          * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
            * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2)) := by ring
  calc ‖(flatIntegerLatticePacketSeparatorData w hdistinct target m hm).bump.1 y‖
        * (‖(gaussianFlatSeedData (fun i => B * σ i) (w target) hm).damping.1 y‖
          * ‖MvPolynomial.eval y P‖)
      ≤ Cb * (((C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
          * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
        * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2))) :=
        mul_le_mul h1 hstep (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCb0
    _ = Cb * ((C₀ * ∑ r ∈ Finset.range m, (1 + C₀) ^ r)
          * (Cp * ∏ i, (1 + 2 * R) ^ (P.degreeOf i)))
        * ((∏ i, (1 + |v i|) ^ (P.degreeOf i))
          * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2)) := by ring

end

end GaloisForLFunctions.HTGeometry
