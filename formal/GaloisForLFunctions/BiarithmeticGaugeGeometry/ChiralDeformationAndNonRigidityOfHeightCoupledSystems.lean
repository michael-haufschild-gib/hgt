import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ExteriorAndHeightCoupledQuartetContractions
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.KernelCountsAreBlindToComplexQuartets
import GaloisForLFunctions.StripBochnerWeilForcing.CollectivePoleRepulsion
import GaloisForLFunctions.StripBochnerWeilForcing.TheSimplePoleClassIsZeta
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Chiral Deformations, Non-Rigidity of Height-Coupled Systems, and the Central Vanishing Ceiling

In degree `1` (`κ = 1, d = 1`), `StripBochnerWeilForcing` proves that `CompletedPositiveSystem 1 1`
collapses up to nonzero real scalars to `ℝ^× · ζ` (`completedPositiveSystem_one_one_eq_zeta`).
To eliminate off-critical complex quartets `{1/2 ± a ± iγ}` at zero boundary pole cost (`Δκ = 0`),
`ArithmeticCorrespondencePositivity` lifts `ζ` to the degree-`4` height-coupled carrier
`ζ_γ(s) = ζ(s)² ζ(s + iγ) ζ(s − iγ)` inside `HeightCoupledSystem 2 1 1 γ`. A natural two-sided
uniqueness conjecture (`CoupledRigid γ`) asks whether `HeightCoupledSystem 2 1 1 γ` also collapses
to `ℝ^× · ζ_γ`.

This module resolves that question in the negative and extracts the exact chiral positive survivor:

1. **Bochner positivity of outward critical-line splitting (`criticalSplitMultiplier`,
   `isEvenPosDef_criticalSplitMultiplier`).**
   For every real shift `β ∈ ℝ`, the rational multiplier
   `W_β(s) = ((s − 1/2)² + β²) / (s − 1/2)²`
   has nonnegative Laplace–Bochner scale weight `2 e^{-(σ - 1/2) t} (1 − cos(β t)) ≥ 0` and hence
   even positive-definite vertical `−logDeriv` sections on `σ > 1`.

2. **Unconditional disproof of `CoupledRigid γ` at infinitely many Hardy ordinates
   (`exists_criticalSplit_deformation_of_xi_zero`, `not_coupledRigid_of_xi_critical_zero`,
   `exists_gt_not_coupledRigid`, `not_forall_coupledRigid`).**
   At every ordinate `γ` where `ξ(1/2 + iγ) = 0`, `Λ_γ(s) = (2ξ(s))² (2ξ(s + iγ)) (2ξ(s − iγ))`
   vanishes at `s = 1/2` to order `≥ 2`. Multiplying `(ζ_γ, Λ_γ)` by `W_β` (`β ≠ 0`) cancels the
   double pole of `W_β` against the double zero of `Λ_γ`, producing a continuous 1-parameter family
   `(F_β, Λ_β) ∈ HeightCoupledSystem 2 1 1 γ` that is **not** scalar-proportional to `ζ_γ`. By
   Hardy's theorem (`completedPositiveSystem_one_critical_zeros`), `¬ CoupledRigid γ` holds at
   unboundedly many critical ordinates `γ → +∞`.

3. **Chiral Deformation Law (`not_isEvenPosDef_inwardCollapseMultiplier`).**
   While outward splitting `W_β` (`Δ ord_{1/2} = −2`) is Bochner-positive, its inverse inward
   critical collapse `W_β⁻¹(s) = (s − 1/2)² / ((s − 1/2)² + β²)` (`Δ ord_{1/2} = +2`, `β ≠ 0`) has
   negative Post–Widder scale weight at `t = π / |β|` and violates the real-anchor law, so its
   vertical `−logDeriv` sections are **not** positive definite on `σ > 1`.

4. **Discrete Log-Lattice vs. Continuous Hadamard Scale Separation
   (`tendsto_cube_mul_zero_of_dirichletLatticeDecay`,
   `tendsto_cube_mul_neg_logDeriv_criticalSplit`,
   `tendsto_cube_mul_neg_logDeriv_coupledQuartetSymSquare`,
   `criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice`).**
   Every convergent non-trivial Dirichlet log-lattice series has exponential `O(2^{-σ})` decay of
   `−(log F)'(σ)` as `σ → +∞` (forcing `σ³ (−(log F)'(σ)) → 0`), whereas both `W_β` (`β ≠ 0`) and
   `coupledQuartetSymSquare b a γ` (`a > 0`) exhibit algebraic `Θ(σ^{-3})` asymptotics with positive
   limits `2 β² > 0` and `4 b² + 4 a² > 0`. Thus finite rational Hadamard surgery always exits the
   discrete integer log-lattice.

5. **The Positive Survivor: `CentralVanishingCeiling γ`
   (`CentralVanishingCeiling`, `criticalSplit_strictly_below_centralCeiling`,
   `xi_ne_zero_of_centralVanishingCeiling`, `riemannHypothesis_of_forall_centralVanishingCeiling`).**
   Replacing two-sided scalar rigidity with the one-sided upper bound
   `ord_{1/2}(Λ) ≤ ord_{1/2}(Λ_γ)` across `HeightCoupledSystem 2 1 1 γ` **survives** every outward
   `W_β` deformation (`ord_{1/2}(Λ_β) = ord_{1/2}(Λ_γ) − 2 < ord_{1/2}(Λ_γ)`) while still
   **unconditionally excluding** off-critical quartets (`ord_{1/2}(Λ_c) = ord_{1/2}(Λ_γ) + 4`) and
   implying `RiemannHypothesis`.
-/

open Complex Filter Topology Set MeasureTheory Finset
open scoped ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity MultiplicativePositivityGeometry
  StripBochnerWeilForcing HTGeometry

/-! ## §1. Two-sided coupled rigidity vs. the one-sided central vanishing ceiling -/

/-- Canonical membership of `ζ_γ` in `HeightCoupledSystem 2 1 1 γ`. -/
theorem zeta_mem_heightCoupledSystem (γ : ℝ) :
    HeightCoupledSystem 2 1 1 γ (heightCoupledF riemannZeta γ)
      (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) :=
  CompletedPositiveSystem.heightCouple completedPositiveSystem_riemannZeta γ

/-- **Two-sided scalar rigidity** of `HeightCoupledSystem 2 1 1 γ`: every member is a nonzero real
scalar multiple of `ζ_γ` on `Re s > 1`. -/
def CoupledRigid (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, HeightCoupledSystem 2 1 1 γ F Λ →
    ∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → F s = K * heightCoupledF riemannZeta γ s

/-- **One-sided chiral survivor (`CentralVanishingCeiling γ`)**: no member of
`HeightCoupledSystem 2 1 1 γ` can exceed the central vanishing order of `Λ_γ` at `s = 1/2`. -/
def CentralVanishingCeiling (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, HeightCoupledSystem 2 1 1 γ F Λ →
    (analyticOrderAt Λ (1 / 2)).toNat ≤
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat

/-- Outward critical-line splitting multiplier `W_β(s) = ((s − 1/2)² + β²) / (s − 1/2)²`, moving a
double zero at `1/2` outward along `Re s = 1/2` to `{1/2 + iβ, 1/2 − iβ}`. -/
def criticalSplitMultiplier (β : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) / (s - 1 / 2) ^ 2

/-- Inward critical-line collapse multiplier `W_β⁻¹(s) = (s − 1/2)² / ((s − 1/2)² + β²)`, moving
`{1/2 + iβ, 1/2 − iβ}` inward onto `1/2`. -/
def inwardCollapseMultiplier (β : ℝ) (s : ℂ) : ℂ :=
  (s - 1 / 2) ^ 2 / ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2)

/-! ## §2. Bochner positivity of outward critical-line splitting `W_β` -/

private theorem sq_add_sq_factor (w : ℂ) (x β : ℝ) :
    (w - (x : ℂ)) ^ 2 + (β : ℂ) ^ 2 =
      (w - ((x : ℂ) + (β : ℂ) * I)) * (w - ((x : ℂ) - (β : ℂ) * I)) := by
  calc (w - (x : ℂ)) ^ 2 + (β : ℂ) ^ 2
      = (w - (x : ℂ)) ^ 2 - ((β : ℂ) * I) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
    _ = (w - ((x : ℂ) + (β : ℂ) * I)) * (w - ((x : ℂ) - (β : ℂ) * I)) := by ring

private theorem re_one_div_laplace_cos (a b : ℝ) (ha : 0 < a) :
    (1 / ((a : ℂ) + (b : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0, Real.exp (-a * t) * Real.cos (b * t) := by
  set w : ℂ := -((a : ℂ) + (b : ℂ) * I)
  have hw_re : w.re < 0 := by simp [w]; linarith
  have hint_c : IntegrableOn (fun t : ℝ => Complex.exp (w * t)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hw_re 0
  have hval := integral_exp_mul_complex_Ioi hw_re 0
  have hrhs_eq : -Complex.exp (w * (0 : ℝ)) / w = 1 / ((a : ℂ) + (b : ℂ) * I) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    dsimp only [w]
    rw [div_neg, neg_div, neg_neg]
  rw [hrhs_eq] at hval
  have hre_int : (∫ t : ℝ in Ioi 0, Complex.exp (w * t)).re =
      ∫ t : ℝ in Ioi 0, (Complex.exp (w * t)).re :=
    (Complex.reCLM.integral_comp_comm hint_c).symm
  rw [← hval, hre_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hw_t_re : (w * (t : ℂ)).re = -a * t := by simp [w]
  have hw_t_im : (w * (t : ℂ)).im = -(b * t) := by simp [w]
  rw [Complex.exp_re, hw_t_re, hw_t_im, Real.cos_neg]

private theorem integrableOn_exp_cos_Ioi (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * Real.cos (b * t)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0)
    ((Continuous.aestronglyMeasurable (by fun_prop)).restrict)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

private theorem isEvenPosDef_of_laplace_cos {w φ : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hw_cont : Continuous w)
    (hw_nn : ∀ t : ℝ, 0 < t → 0 ≤ w t)
    (hw_le : ∀ t : ℝ, 0 < t → w t ≤ C * Real.exp (-a * t))
    (hφ : ∀ u : ℝ, φ u = ∫ t : ℝ in Ioi 0, w t * Real.cos (t * u)) :
    IsEvenPosDef φ := by
  have hint_dom : IntegrableOn (fun t : ℝ => C * Real.exp (-a * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (show -a < 0 by linarith) 0).const_mul C
  have hint_ker : ∀ u : ℝ,
      IntegrableOn (fun t : ℝ => w t * Real.cos (t * u)) (Ioi 0) := by
    intro u
    refine Integrable.mono' hint_dom
      ((Continuous.aestronglyMeasurable (by fun_prop)).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw_nn t ht)]
    exact (mul_le_of_le_one_right (hw_nn t ht) (Real.abs_cos_le_one _)).trans (hw_le t ht)
  refine ⟨fun u => ?_, fun n x c => ?_⟩
  · rw [hφ (-u), hφ u]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_neg, Real.cos_neg]
  · have hsum_int : ∑ i, ∑ j, c i * c j * φ (x i - x j) =
        ∫ t : ℝ in Ioi 0, w t * ∑ i, ∑ j, c i * c j * Real.cos (t * (x i - x j)) := by
      simp_rw [hφ, ← integral_const_mul]
      have h1 : ∀ i : Fin n,
          ∑ j : Fin n, ∫ t : ℝ in Ioi 0, c i * c j * (w t * Real.cos (t * (x i - x j))) =
          ∫ t : ℝ in Ioi 0, ∑ j : Fin n, c i * c j * (w t * Real.cos (t * (x i - x j))) :=
        fun i => (integral_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)).symm
      simp_rw [h1]
      rw [← integral_finsetSum Finset.univ fun i _ =>
        integrable_finsetSum Finset.univ fun j _ =>
          (hint_ker (x i - x j)).const_mul (c i * c j)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsum_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    refine mul_nonneg (hw_nn t ht) ?_
    rw [gram_cos_eq]
    positivity

private theorem isEvenPosDef_add_bgg {φ ψ : ℝ → ℝ}
    (hφ : IsEvenPosDef φ) (hψ : IsEvenPosDef ψ) :
    IsEvenPosDef (fun u => φ u + ψ u) where
  even u := by rw [hφ.even, hψ.even]
  posDef n x c := by
    have h : (∑ i, ∑ j, c i * c j * (φ (x i - x j) + ψ (x i - x j))) =
        (∑ i, ∑ j, c i * c j * φ (x i - x j)) + ∑ i, ∑ j, c i * c j * ψ (x i - x j) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    rw [h]
    exact add_nonneg (hφ.posDef n x c) (hψ.posDef n x c)

/-- Exact Laplace–cosine representation of `Re(−W_β'/W_β)(σ + iu)` on `σ > 1/2`. -/
theorem re_neg_logDeriv_criticalSplitMultiplier_eq (β : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) (u : ℝ) :
    (-logDeriv (criticalSplitMultiplier β) ((σ : ℂ) + (u : ℂ) * I)).re =
      ∫ t : ℝ in Ioi 0,
        (2 * Real.exp (-(σ - 1 / 2) * t) * (1 - Real.cos (β * t))) * Real.cos (t * u) := by
  set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
  set z₁ : ℂ := (1 / 2 : ℂ) + (β : ℂ) * I
  set z₂ : ℂ := (1 / 2 : ℂ) - (β : ℂ) * I
  have hs0 : s - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def] at this; linarith
  have hz₁ : s - z₁ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def, z₁] at this; linarith
  have hz₂ : s - z₂ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hs_def, z₂] at this; linarith
  have hnum_eq : (fun w : ℂ => (w - 1 / 2) ^ 2 + (β : ℂ) ^ 2) =
      fun w : ℂ => (w - z₁) * (w - z₂) := by
    funext w
    have h := sq_add_sq_factor w (1 / 2) β
    have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hc] at h
    exact h
  have hcs_eq : criticalSplitMultiplier β =
      fun w : ℂ => ((w - z₁) * (w - z₂)) / (w - 1 / 2) ^ 2 := by
    funext w
    unfold criticalSplitMultiplier
    rw [congrFun hnum_eq w]
  have hd_sub : ∀ c : ℂ, DifferentiableAt ℂ (fun w : ℂ => w - c) s := fun _ => by fun_prop
  have hd_lin : ∀ c : ℂ, logDeriv (fun w : ℂ => w - c) s = 1 / (s - c) := fun c => by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  have hld : -logDeriv (criticalSplitMultiplier β) s =
      2 * (1 / (s - 1 / 2)) - (1 / (s - z₁) + 1 / (s - z₂)) := by
    rw [hcs_eq,
        logDeriv_div (f := fun w => (w - z₁) * (w - z₂))
          (g := fun w => (w - 1 / 2) ^ 2) s (mul_ne_zero hz₁ hz₂) (pow_ne_zero 2 hs0)
          ((hd_sub z₁).mul (hd_sub z₂)) ((hd_sub (1 / 2)).fun_pow 2),
        logDeriv_mul (f := fun w => w - z₁) (g := fun w => w - z₂) s hz₁ hz₂
          (hd_sub z₁) (hd_sub z₂),
        logDeriv_fun_pow (hd_sub (1 / 2)) 2,
        hd_lin, hd_lin, hd_lin]
    push_cast; ring
  have e₀ : s - 1 / 2 = (((σ - 1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
    dsimp [s]; push_cast; ring
  have e₁ : s - z₁ = (((σ - 1 / 2 : ℝ) : ℂ) + ((u - β : ℝ) : ℂ) * I) := by
    dsimp [s, z₁]; push_cast; ring
  have e₂ : s - z₂ = (((σ - 1 / 2 : ℝ) : ℂ) + ((u + β : ℝ) : ℂ) * I) := by
    dsimp [s, z₂]; push_cast; ring
  have hre : (-logDeriv (criticalSplitMultiplier β) s).re =
      2 * (1 / (s - 1 / 2)).re - ((1 / (s - z₁)).re + (1 / (s - z₂)).re) := by
    rw [hld]
    have h2 : (2 * (1 / (s - 1 / 2))).re = 2 * (1 / (s - 1 / 2)).re := by
      simp [Complex.mul_re]
    rw [Complex.sub_re, Complex.add_re, h2]
  rw [hre, e₀, e₁, e₂,
      re_one_div_laplace_cos (σ - 1 / 2) u (by linarith),
      re_one_div_laplace_cos (σ - 1 / 2) (u - β) (by linarith),
      re_one_div_laplace_cos (σ - 1 / 2) (u + β) (by linarith)]
  have hi₀ := integrableOn_exp_cos_Ioi (σ - 1 / 2) u (by linarith)
  have hi₁ := integrableOn_exp_cos_Ioi (σ - 1 / 2) (u - β) (by linarith)
  have hi₂ := integrableOn_exp_cos_Ioi (σ - 1 / 2) (u + β) (by linarith)
  symm
  calc ∫ t : ℝ in Ioi 0,
        (2 * Real.exp (-(σ - 1 / 2) * t) * (1 - Real.cos (β * t))) * Real.cos (t * u)
      = ∫ t : ℝ in Ioi 0,
          (2 * (Real.exp (-(σ - 1 / 2) * t) * Real.cos (u * t)) -
            (Real.exp (-(σ - 1 / 2) * t) * Real.cos ((u - β) * t) +
             Real.exp (-(σ - 1 / 2) * t) * Real.cos ((u + β) * t))) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        have hc₁ : Real.cos ((u - β) * t) =
            Real.cos (t * u) * Real.cos (β * t) + Real.sin (t * u) * Real.sin (β * t) := by
          rw [show (u - β) * t = t * u - β * t by ring, Real.cos_sub]
        have hc₂ : Real.cos ((u + β) * t) =
            Real.cos (t * u) * Real.cos (β * t) - Real.sin (t * u) * Real.sin (β * t) := by
          rw [show (u + β) * t = t * u + β * t by ring, Real.cos_add]
        rw [hc₁, hc₂, show u * t = t * u by ring]
        ring
    _ = 2 * (∫ t : ℝ in Ioi 0, Real.exp (-(σ - 1 / 2) * t) * Real.cos (u * t)) -
          ((∫ t : ℝ in Ioi 0, Real.exp (-(σ - 1 / 2) * t) * Real.cos ((u - β) * t)) +
           (∫ t : ℝ in Ioi 0, Real.exp (-(σ - 1 / 2) * t) * Real.cos ((u + β) * t))) := by
        rw [integral_sub (hi₀.const_mul 2) (hi₁.add hi₂), integral_const_mul, integral_add hi₁ hi₂]

/-- **Bochner Positivity of Outward Critical Splitting (`isEvenPosDef_criticalSplitMultiplier`).**
For every `β ∈ ℝ` and `σ > 1`, `u ↦ Re(−W_β'/W_β)(σ + iu)` is even and positive definite. -/
theorem isEvenPosDef_criticalSplitMultiplier (β : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    IsEvenPosDef fun u : ℝ =>
      (-logDeriv (criticalSplitMultiplier β) ((σ : ℂ) + (u : ℂ) * I)).re := by
  refine isEvenPosDef_of_laplace_cos (C := 4) (a := σ - 1 / 2) (by linarith) (by fun_prop)
    (fun t _ => ?_) (fun t _ => ?_)
    (re_neg_logDeriv_criticalSplitMultiplier_eq β (by linarith))
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  · have hc : 1 - Real.cos (β * t) ≤ 2 := by linarith [Real.neg_one_le_cos (β * t)]
    calc 2 * Real.exp (-(σ - 1 / 2) * t) * (1 - Real.cos (β * t))
        ≤ 2 * Real.exp (-(σ - 1 / 2) * t) * 2 :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 4 * Real.exp (-(σ - 1 / 2) * t) := by ring

/-! ## §3. Unconditional disproof of `CoupledRigid γ` at Hardy critical zeros -/

private theorem orderOneEnvelope_sub_const_bgg (c : ℂ) :
    OrderOneEnvelope (fun s : ℂ => s - c) :=
  (RHTower.orderOneEnvelope_id.add (orderOneEnvelope_const (-c))).congr fun s => by ring

private theorem orderOneEnvelope_criticalQuad (β : ℝ) :
    OrderOneEnvelope (fun s : ℂ => (s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := by
  have h1 := orderOneEnvelope_sub_const_bgg ((1 / 2 : ℂ) + (β : ℂ) * I)
  have h2 := orderOneEnvelope_sub_const_bgg ((1 / 2 : ℂ) - (β : ℂ) * I)
  refine (h1.mul h2).congr fun s => ?_
  have hf := sq_add_sq_factor s (1 / 2) β
  have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [hc] at hf
  exact hf.symm

private theorem dslope_entire_and_orderOne_bgg {f : ℂ → ℂ} {z₀ : ℂ}
    (hd : Differentiable ℂ f) (hf : OrderOneEnvelope f) (hz₀ : f z₀ = 0) :
    Differentiable ℂ (dslope f z₀) ∧
      OrderOneEnvelope (dslope f z₀) ∧
      (∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s) ∧
      analyticOrderAt f z₀ = (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
  have hD : Differentiable ℂ (dslope f z₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 z₀)).mpr
      hd.differentiableOn
  have hid : ∀ s : ℂ, (s - z₀) * dslope f z₀ s = f s := fun s => by
    simpa [hz₀, smul_eq_mul] using sub_smul_dslope f z₀ s
  have hfeq : (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) = f :=
    funext fun s => by simpa using hid s
  have han_lin : AnalyticAt ℂ ((fun x : ℂ => x - z₀) ^ 1) z₀ := by
    change AnalyticAt ℂ (fun x : ℂ => (x - z₀) ^ 1) z₀
    fun_prop
  have hord : analyticOrderAt f z₀ = (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
    have hprod : analyticOrderAt (((fun x : ℂ => x - z₀) ^ 1) * dslope f z₀) z₀ =
        (1 : ℕ) + analyticOrderAt (dslope f z₀) z₀ := by
      rw [analyticOrderAt_mul han_lin (hD.analyticAt z₀), analyticOrderAt_centeredMonomial]
    rwa [hfeq] at hprod
  refine ⟨hD, ?_, hid, hord⟩
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    hD.continuous.continuousOn
  obtain ⟨C, _, hb⟩ := hf
  obtain ⟨D, _, hDb⟩ := orderOneEnvelope_const (B : ℂ)
  refine ⟨C + D, by linarith, fun z => ?_⟩
  by_cases hz : ‖z - z₀‖ ≤ 1
  · have hmem : z ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hz
    have hBabs : B ≤ ‖(B : ℂ)‖ := by simpa using le_abs_self B
    exact (hB z hmem).trans (hBabs.trans ((hDb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : D ≤ C + D) z))))
  · have hn := congrArg norm (hid z)
    rw [norm_mul] at hn
    have hle : ‖dslope f z₀ z‖ ≤ ‖f z‖ := by
      have hz1 : 1 ≤ ‖z - z₀‖ := le_of_not_ge hz
      nlinarith [norm_nonneg (dslope f z₀ z)]
    exact hle.trans ((hb z).trans
      (Real.exp_le_exp.mpr (orderOneWeight_mono (by linarith : C ≤ C + D) z)))

private theorem continuous_eq_of_mul_sq_half {g₁ g₂ : ℂ → ℂ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (hmul : ∀ z : ℂ, g₁ z * (z - 1 / 2) ^ 2 = g₂ z * (z - 1 / 2) ^ 2) :
    ∀ s : ℂ, g₁ s = g₂ s := by
  intro s
  by_cases hs : s = 1 / 2
  · subst hs
    have hev : g₁ =ᶠ[𝓝[≠] (1 / 2 : ℂ)] g₂ := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_right_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr hz)) (hmul z)
    exact tendsto_nhds_unique (hg₁.continuousAt.continuousWithinAt.congr' hev)
      hg₂.continuousAt.continuousWithinAt
  · exact mul_right_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr hs)) (hmul s)

/-- **Outward Critical-Splitting Deformation (`exists_criticalSplit_deformation_of_xi_zero`).**
Whenever `ξ(1/2 + iγ) = 0`, for every `β ≠ 0` there exists an entire completion `Λ_β` such that
`(ζ_γ · W_β, Λ_β) ∈ HeightCoupledSystem 2 1 1 γ`, its central vanishing order drops by `2`
(`ord_{1/2}(Λ_β) + 2 = ord_{1/2}(Λ_γ)`), and `ζ_γ · W_β` is not a real scalar multiple of `ζ_γ`. -/
theorem exists_criticalSplit_deformation_of_xi_zero {γ β : ℝ}
    (hxi : RHTower.xi (1 / 2 + (γ : ℂ) * I) = 0) (hβ : β ≠ 0) :
    ∃ Λβ : ℂ → ℂ,
      HeightCoupledSystem 2 1 1 γ
        (fun s => heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s) Λβ ∧
      (analyticOrderAt Λβ (1 / 2)).toNat + 2 =
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat ∧
      ¬ (∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re →
        heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s =
          K * heightCoupledF riemannZeta γ s) := by
  have hZ := completedPositiveSystem_riemannZeta
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ : ℂ → ℂ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ
  have h2xi_zero : (fun s => 2 * RHTower.xi s) (1 / 2 + (γ : ℂ) * I) = 0 := by
    simp only [hxi, mul_zero]
  have hord_shift : 1 ≤ (analyticOrderAt (fun s => 2 * RHTower.xi s)
      (1 / 2 + (γ : ℂ) * I)).toNat :=
    hZ.one_le_order_toNat_of_eq_zero h2xi_zero
  have hord_Λγ : 2 ≤ (analyticOrderAt Λγ (1 / 2)).toNat := by
    have h0 := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hZ γ (1 / 2)
    have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hhalf] at h0
    change (analyticOrderAt Λγ (1 / 2)).toNat = _ at h0
    omega
  have hΛγ_zero : Λγ (1 / 2) = 0 := hHC0.eq_zero_of_one_le_order_toNat (by omega)
  obtain ⟨hd₁, ho₁, heq₁, hord₁⟩ :=
    dslope_entire_and_orderOne_bgg hHC0.entire_Λ hHC0.orderOne_Λ hΛγ_zero
  have hd₁_ord_ge1 : (1 : ℕ∞) ≤ analyticOrderAt (dslope Λγ (1 / 2)) (1 / 2) := by
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hHC0.orderAt_ne_top (1 / 2))
    rw [← hm, ENat.toNat_coe] at hord_Λγ
    rw [← hm] at hord₁
    rcases eq_top_or_lt_top (analyticOrderAt (dslope Λγ (1 / 2)) (1 / 2)) with htop | hlt
    · rw [htop]; exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hlt.ne
      rw [← hk] at hord₁ ⊢
      norm_cast at hord₁ ⊢
      omega
  have hd₁_zero : dslope Λγ (1 / 2) (1 / 2) = 0 := by
    by_contra hnz
    rw [(hd₁.analyticAt (1 / 2)).analyticOrderAt_eq_zero.mpr hnz] at hd₁_ord_ge1
    exact absurd hd₁_ord_ge1 (by simp)
  obtain ⟨hdQ, hoQ, heq₂, hord₂⟩ :=
    dslope_entire_and_orderOne_bgg hd₁ ho₁ hd₁_zero
  set Q : ℂ → ℂ := dslope (dslope Λγ (1 / 2)) (1 / 2)
  have hQ_fac : ∀ s : ℂ, (s - 1 / 2) ^ 2 * Q s = Λγ s := fun s => by
    calc (s - 1 / 2) ^ 2 * Q s
        = (s - 1 / 2) * ((s - 1 / 2) * Q s) := by ring
      _ = (s - 1 / 2) * dslope Λγ (1 / 2) s := by rw [heq₂ s]
      _ = Λγ s := heq₁ s
  let Λβ : ℂ → ℂ := fun s => Q s * ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2)
  have hdΛβ : Differentiable ℂ Λβ := hdQ.mul (by fun_prop)
  have hoΛβ : OrderOneEnvelope Λβ := hoQ.mul (orderOneEnvelope_criticalQuad β)
  have hrel : ∀ s : ℂ, Λβ s * (s - 1 / 2) ^ 2 = Λγ s * ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) :=
    fun s => by
      dsimp [Λβ]
      calc Q s * ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) * (s - 1 / 2) ^ 2
          = ((s - 1 / 2) ^ 2 * Q s) * ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := by ring
        _ = Λγ s * ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := by rw [hQ_fac s]
  have hsym_β : ∀ s : ℂ, Λβ (1 - s) = Λβ s := by
    refine continuous_eq_of_mul_sq_half (hdΛβ.continuous.comp (by fun_prop)) hdΛβ.continuous
      fun z => ?_
    have hsq_sym : ((1 - z) - 1 / 2) ^ 2 = (z - 1 / 2) ^ 2 := by ring
    calc Λβ (1 - z) * (z - 1 / 2) ^ 2
        = Λβ (1 - z) * ((1 - z) - 1 / 2) ^ 2 := by rw [hsq_sym]
      _ = Λγ (1 - z) * (((1 - z) - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := hrel (1 - z)
      _ = Λγ z * ((z - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := by rw [hHC0.sym_Λ z, hsq_sym]
      _ = Λβ z * (z - 1 / 2) ^ 2 := (hrel z).symm
  have hconj_β : ∀ s : ℂ, Λβ (starRingEnd ℂ s) = starRingEnd ℂ (Λβ s) := by
    have hinv := continuous_eq_of_mul_sq_half
      (Complex.continuous_conj.comp (hdΛβ.continuous.comp Complex.continuous_conj))
      hdΛβ.continuous fun z => by
        have hsq_conj : starRingEnd ℂ ((starRingEnd ℂ z - 1 / 2) ^ 2) = (z - 1 / 2) ^ 2 := by
          simp [map_ofNat]
        have hquad_conj : starRingEnd ℂ (((starRingEnd ℂ z - 1 / 2) ^ 2 + (β : ℂ) ^ 2)) =
            (z - 1 / 2) ^ 2 + (β : ℂ) ^ 2 := by
          simp [map_ofNat]
        dsimp only [Function.comp_apply]
        calc starRingEnd ℂ (Λβ (starRingEnd ℂ z)) * (z - 1 / 2) ^ 2
            = starRingEnd ℂ (Λβ (starRingEnd ℂ z) * (starRingEnd ℂ z - 1 / 2) ^ 2) := by
                rw [map_mul, hsq_conj]
          _ = starRingEnd ℂ (Λγ (starRingEnd ℂ z) *
                ((starRingEnd ℂ z - 1 / 2) ^ 2 + (β : ℂ) ^ 2)) := by
                rw [hrel (starRingEnd ℂ z)]
          _ = Λγ z * ((z - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := by
                rw [map_mul, hHC0.conj_Λ z, Complex.conj_conj, hquad_conj]
          _ = Λβ z * (z - 1 / 2) ^ 2 := (hrel z).symm
    intro s
    have hs := congrArg (starRingEnd ℂ) (hinv s)
    simpa [Function.comp_apply] using hs
  have hW_nz : ∀ s : ℂ, 1 < s.re → criticalSplitMultiplier β s ≠ 0 := by
    intro s hs
    unfold criticalSplitMultiplier
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hnum_nz : (s - 1 / 2) ^ 2 + (β : ℂ) ^ 2 ≠ 0 := by
      have hf := sq_add_sq_factor s (1 / 2) β
      have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
      rw [hc] at hf; rw [hf]
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    exact div_ne_zero hnum_nz (pow_ne_zero 2 hs_half)
  have hW_diffAt : ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (criticalSplitMultiplier β) s := by
    intro s hs
    unfold criticalSplitMultiplier
    have hs_half : s - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hs_half)
  have hHCβ : HeightCoupledSystem 2 1 1 γ
      (fun s => heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s) Λβ :=
    { degree_pos := hHC0.degree_pos
      diffOn_F := hHC0.diffOn_F.mul (fun s hs => (hW_diffAt s hs).differentiableWithinAt)
      ne_zero_F := fun s hs => mul_ne_zero (hHC0.ne_zero_F s hs) (hW_nz s hs)
      posDef_neg_logDeriv := fun {σ} hσ => by
        have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq : (fun u : ℝ =>
            (-logDeriv (fun s => heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s)
              ((σ : ℂ) + (u : ℂ) * I)).re) =
            fun u : ℝ => (-logDeriv (heightCoupledF riemannZeta γ) ((σ : ℂ) + (u : ℂ) * I)).re +
              (-logDeriv (criticalSplitMultiplier β) ((σ : ℂ) + (u : ℂ) * I)).re := by
          funext u
          set s : ℂ := (σ : ℂ) + (u : ℂ) * I
          have hs : 1 < s.re := by simp [s]; exact hσ
          rw [logDeriv_mul (f := heightCoupledF riemannZeta γ) (g := criticalSplitMultiplier β) s
                (hHC0.ne_zero_F s hs) (hW_nz s hs)
                ((hHC0.diffOn_F s hs).differentiableAt (hopen.mem_nhds hs))
                (hW_diffAt s hs),
              neg_add, Complex.add_re]
        rw [heq]
        exact isEvenPosDef_add_bgg (hHC0.posDef_neg_logDeriv hσ)
          (isEvenPosDef_criticalSplitMultiplier β hσ)
      entire_Λ := hdΛβ
      orderOne_Λ := hoΛβ
      sym_Λ := hsym_β
      conj_Λ := hconj_β
      completed_eq := fun s hs => by
        have hs_sq : (s - 1 / 2) ^ 2 ≠ 0 := pow_ne_zero 2 fun h => by
          have := congrArg Complex.re h; simp at this; linarith
        apply mul_right_cancel₀ hs_sq
        have hW_mul : criticalSplitMultiplier β s * (s - 1 / 2) ^ 2 =
            (s - 1 / 2) ^ 2 + (β : ℂ) ^ 2 :=
          div_mul_cancel₀ _ hs_sq
        calc Λβ s * (s - 1 / 2) ^ 2
            = Λγ s * ((s - 1 / 2) ^ 2 + (β : ℂ) ^ 2) := hrel s
          _ = ((s * (s - 1)) ^ 2 * shiftedPolePoly γ s ^ 1 * coupledGamma γ 1 s *
                heightCoupledF riemannZeta γ s) *
                (criticalSplitMultiplier β s * (s - 1 / 2) ^ 2) := by
              rw [hHC0.completed_eq s hs, hW_mul]
          _ = (s * (s - 1)) ^ 2 * shiftedPolePoly γ s ^ 1 * coupledGamma γ 1 s *
                (heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s) *
                (s - 1 / 2) ^ 2 := by ring }
  have hord_drop : (analyticOrderAt Λβ (1 / 2)).toNat + 2 = (analyticOrderAt Λγ (1 / 2)).toNat := by
    let P_quad : ℂ → ℂ := fun s => (s - 1 / 2) ^ 2 + (β : ℂ) ^ 2
    have hdP : Differentiable ℂ P_quad := by dsimp [P_quad]; fun_prop
    have hP_nz : P_quad (1 / 2) ≠ 0 := by
      dsimp [P_quad]
      simp [pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hβ)]
    have hΛβ_eq : Λβ = Q * P_quad := rfl
    have hord_Λβ_Q : analyticOrderAt Λβ (1 / 2) = analyticOrderAt Q (1 / 2) := by
      rw [hΛβ_eq, analyticOrderAt_mul (hdQ.analyticAt _) (hdP.analyticAt _),
          (hdP.analyticAt _).analyticOrderAt_eq_zero.mpr hP_nz, add_zero]
    have hord_tot : analyticOrderAt Λγ (1 / 2) = (2 : ℕ) + analyticOrderAt Q (1 / 2) := by
      have h11 : ((1 : ℕ) : ℕ∞) + (1 : ℕ) = (2 : ℕ) := by norm_num
      rw [hord₁, hord₂, ← add_assoc, h11]
    have hQ_ntop : analyticOrderAt Q (1 / 2) ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hord_tot
      exact hHC0.orderAt_ne_top (1 / 2) hord_tot
    rw [hord_Λβ_Q, hord_tot, ENat.toNat_add (ENat.coe_ne_top 2) hQ_ntop, ENat.toNat_coe]
    omega
  have hnot_prop : ¬ (∃ K : ℝ, K ≠ 0 ∧ ∀ s : ℂ, 1 < s.re →
      heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s =
        K * heightCoupledF riemannZeta γ s) := by
    rintro ⟨K, -, hK⟩
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    have h3 : (1 : ℝ) < (3 : ℂ).re := by norm_num
    have hF2_nz : heightCoupledF riemannZeta γ 2 ≠ 0 := hHC0.ne_zero_F 2 h2
    have hF3_nz : heightCoupledF riemannZeta γ 3 ≠ 0 := hHC0.ne_zero_F 3 h3
    have hW2 : criticalSplitMultiplier β 2 = (K : ℂ) :=
      mul_left_cancel₀ hF2_nz (by linear_combination hK 2 h2)
    have hW3 : criticalSplitMultiplier β 3 = (K : ℂ) :=
      mul_left_cancel₀ hF3_nz (by linear_combination hK 3 h3)
    have heq23 : (criticalSplitMultiplier β 2).re = (criticalSplitMultiplier β 3).re := by
      rw [hW2, hW3]
    have hval2 : criticalSplitMultiplier β 2 = (((9 / 4 + β ^ 2) / (9 / 4) : ℝ) : ℂ) := by
      unfold criticalSplitMultiplier
      push_cast; norm_num
    have hval3 : criticalSplitMultiplier β 3 = (((25 / 4 + β ^ 2) / (25 / 4) : ℝ) : ℂ) := by
      unfold criticalSplitMultiplier
      push_cast; norm_num
    rw [hval2, hval3, Complex.ofReal_re, Complex.ofReal_re] at heq23
    have hβ_sq : β ^ 2 = 0 := by linarith
    exact hβ (sq_eq_zero_iff.mp hβ_sq)
  exact ⟨Λβ, hHCβ, hord_drop, hnot_prop⟩

/-- **Failure of `CoupledRigid γ` at every critical zero of `ξ`.** -/
theorem not_coupledRigid_of_xi_critical_zero {γ : ℝ}
    (hxi : RHTower.xi (1 / 2 + (γ : ℂ) * I) = 0) :
    ¬ CoupledRigid γ := by
  intro hrig
  obtain ⟨Λβ, hHCβ, -, hnot⟩ := exists_criticalSplit_deformation_of_xi_zero hxi one_ne_zero
  exact hnot (hrig _ _ hHCβ)

/-- **Unbounded Hardy critical ordinates violate `CoupledRigid γ`.** For every threshold `T : ℝ`,
there exists `γ > T` (`γ ≠ 0`) such that `¬ CoupledRigid γ`. -/
theorem exists_gt_not_coupledRigid (T : ℝ) :
    ∃ γ : ℝ, T < γ ∧ γ ≠ 0 ∧ ¬ CoupledRigid γ := by
  obtain ⟨γ, hγ_gt, h2xi⟩ :=
    completedPositiveSystem_one_critical_zeros completedPositiveSystem_riemannZeta (max T 0)
  have hT : T < γ := lt_of_le_of_lt (le_max_left T 0) hγ_gt
  have hpos : 0 < γ := lt_of_le_of_lt (le_max_right T 0) hγ_gt
  have hxi : RHTower.xi (1 / 2 + (γ : ℂ) * I) = 0 := by
    rcases mul_eq_zero.mp h2xi with h2 | hz
    · norm_num at h2
    · exact hz
  exact ⟨γ, hT, hpos.ne', not_coupledRigid_of_xi_critical_zero hxi⟩

/-- **Unconditional disproof of universal two-sided coupled rigidity.** -/
theorem not_forall_coupledRigid : ¬ (∀ γ : ℝ, γ ≠ 0 → CoupledRigid γ) := by
  intro hall
  obtain ⟨γ, -, hγ0, hnot⟩ := exists_gt_not_coupledRigid 0
  exact hnot (hall γ hγ0)

/-! ## §4. Chiral Deformation Law: inward critical collapse fails Bochner positivity -/

/-- **Chiral Deformation Law (`not_isEvenPosDef_inwardCollapseMultiplier`).**
Whereas outward critical splitting `W_β` (`Δ ord_{1/2} = −2`) has positive-definite vertical
`−logDeriv` sections on `σ > 1`, inward critical collapse `W_β⁻¹` (`Δ ord_{1/2} = +2`, `β ≠ 0`)
violates the Post–Widder real-anchor law (`c(1/2 + i|β|) = 1 > −2 = c(1/2)`), so its vertical
`−logDeriv` sections are **not** positive definite across `σ > 1`. -/
theorem not_isEvenPosDef_inwardCollapseMultiplier {β : ℝ} (hβ : β ≠ 0) :
    ¬ ∀ σ : ℝ, 1 < σ → IsEvenPosDef fun u : ℝ =>
      (-logDeriv (inwardCollapseMultiplier β) ((σ : ℂ) + (u : ℂ) * I)).re := by
  classical
  intro hall
  set b₀ : ℝ := |β|
  have hb₀_pos : 0 < b₀ := abs_pos.mpr hβ
  let z₀ : ℂ := ((1 / 2 : ℝ) : ℂ)
  let z₁ : ℂ := ((1 / 2 : ℝ) : ℂ) + (b₀ : ℂ) * I
  let z₂ : ℂ := ((1 / 2 : ℝ) : ℂ) - (b₀ : ℂ) * I
  let S : Finset ℂ := {z₀, z₁, z₂}
  let c : ℂ → ℝ := fun z =>
    if z = z₀ then -2
    else if z = z₁ ∨ z = z₂ then 1
    else 0
  have h01 : z₀ ≠ z₁ := fun h => by
    have := congrArg Complex.im h; simp [z₀, z₁] at this; linarith
  have h02 : z₀ ≠ z₂ := fun h => by
    have := congrArg Complex.im h; simp [z₀, z₂] at this; linarith
  have h12 : z₁ ≠ z₂ := fun h => by
    have := congrArg Complex.im h; simp [z₁, z₂] at this; linarith
  have hconj0 : conj z₀ = z₀ := Complex.conj_ofReal _
  have hconj1 : conj z₁ = z₂ := by simp [z₁, z₂, map_ofNat]; ring
  have hconj2 : conj z₂ = z₁ := by simp [z₁, z₂, map_ofNat]
  have hS_conj : ∀ z ∈ S, conj z ∈ S := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl | rfl
    · left; exact hconj0
    · right; right; exact hconj1
    · right; left; exact hconj2
  have hc_conj : ∀ z ∈ S, c (conj z) = c z := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · rw [hconj0]
    · rw [hconj1]; simp [c, h01.symm, h02.symm]
    · rw [hconj2]; simp [c, h01.symm, h02.symm]
  have hS_re₁ : ∀ z ∈ S, z.re ≤ 1 := by
    intro z hz
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> (simp [z₀, z₁, z₂]; norm_num)
  have hmax : ∀ z ∈ S, c z ≠ 0 → z.re ≤ 1 / 2 := by
    intro z hz _
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [z₀, z₁, z₂]
  have hpd : ∀ σ : ℝ, 1 < σ →
      IsPosDef fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
    intro σ hσ
    have heq_fn : (fun u : ℝ => (polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (-logDeriv (inwardCollapseMultiplier β) ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      congr 1
      set s : ℂ := (σ : ℂ) + (u : ℂ) * I with hs_def
      have hs0 : s - z₀ ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp [hs_def, z₀] at this; linarith
      have hs1 : s - z₁ ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp [hs_def, z₁] at this; linarith
      have hs2 : s - z₂ ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp [hs_def, z₂] at this; linarith
      have hden_eq : (fun w : ℂ => (w - 1 / 2) ^ 2 + (β : ℂ) ^ 2) =
          fun w : ℂ => (w - z₁) * (w - z₂) := by
        funext w
        have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
        have hb_sq : (b₀ : ℂ) ^ 2 = (β : ℂ) ^ 2 := by
          dsimp [b₀]; norm_cast; exact sq_abs β
        calc (w - 1 / 2) ^ 2 + (β : ℂ) ^ 2
            = (w - ((1 / 2 : ℝ) : ℂ)) ^ 2 + (b₀ : ℂ) ^ 2 := by rw [hhalf, hb_sq]
          _ = (w - z₁) * (w - z₂) := sq_add_sq_factor w (1 / 2) b₀
      have hnum_eq : (fun w : ℂ => (w - 1 / 2) ^ 2) = fun w : ℂ => (w - z₀) ^ 2 := by
        funext w; dsimp [z₀]; norm_num
      have hic_eq : inwardCollapseMultiplier β =
          fun w : ℂ => (w - z₀) ^ 2 / ((w - z₁) * (w - z₂)) := by
        funext w
        unfold inwardCollapseMultiplier
        rw [congrFun hnum_eq w, congrFun hden_eq w]
      have hd_sub : ∀ c₀ : ℂ, DifferentiableAt ℂ (fun w : ℂ => w - c₀) s := fun _ => by fun_prop
      have hd_lin : ∀ c₀ : ℂ, logDeriv (fun w : ℂ => w - c₀) s = 1 / (s - c₀) := fun c₀ => by
        rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
      rw [hic_eq,
          logDeriv_div (f := fun w => (w - z₀) ^ 2) (g := fun w => (w - z₁) * (w - z₂)) s
            (pow_ne_zero 2 hs0) (mul_ne_zero hs1 hs2)
            ((hd_sub z₀).fun_pow 2) ((hd_sub z₁).mul (hd_sub z₂)),
          logDeriv_fun_pow (hd_sub z₀) 2,
          logDeriv_mul (f := fun w => w - z₁) (g := fun w => w - z₂) s hs1 hs2
            (hd_sub z₁) (hd_sub z₂),
          hd_lin, hd_lin, hd_lin]
      unfold polarSum
      dsimp [S]
      rw [Finset.sum_insert (by simp [h01, h02]),
          Finset.sum_insert (by simp [h12]),
          Finset.sum_singleton]
      have hc0 : c z₀ = -2 := by simp [c]
      have hc1 : c z₁ = 1 := by simp [c, h01.symm]
      have hc2 : c z₂ = 1 := by simp [c, h02.symm]
      rw [hc0, hc1, hc2]
      push_cast; ring
    rw [heq_fn]
    exact (hall σ hσ).posDef
  have hz₁_mem : (((1 / 2 : ℝ) : ℂ) + (b₀ : ℂ) * I) ∈ S := by
    change z₁ ∈ S; simp [S]
  have hz₁_pos : 0 < c (((1 / 2 : ℝ) : ℂ) + (b₀ : ℂ) * I) := by
    change 0 < c z₁; simp [c, h01.symm]
  obtain ⟨-, hle⟩ := real_anchor_of_posDef_polarSum hS_conj hc_conj hS_re₁ hpd hmax
    hb₀_pos.ne' hz₁_mem hz₁_pos
  have hc1_val : c (((1 / 2 : ℝ) : ℂ) + (b₀ : ℂ) * I) = 1 := by
    change c z₁ = 1; simp [c, h01.symm]
  have hc0_val : c ((1 / 2 : ℝ) : ℂ) = -2 := by
    change c z₀ = -2; simp [c]
  linarith

/-! ## §5. Discrete Dirichlet Log-Lattice vs. Continuous Hadamard Scale Separation -/

/-- Exponential `O(2^{-σ})` right-half-plane decay characteristic of the real logarithmic derivative
`−(log F)'(σ)` of any non-constant ordinary Dirichlet series `1 + ∑_{n ≥ 2} c_n n^{-s}` supported on
the discrete integer log-lattice `{log n : n ≥ 2}`. -/
def HasDirichletLatticeDecay (G : ℝ → ℝ) : Prop :=
  ∃ C σ₀ : ℝ, ∀ σ : ℝ, σ₀ ≤ σ → |G σ| ≤ C * (2 : ℝ) ^ (-σ)

/-- Any function with `O(2^{-σ})` Dirichlet log-lattice decay satisfies `lim_{σ → +∞} σ³ G(σ) = 0`. -/
theorem tendsto_cube_mul_zero_of_dirichletLatticeDecay {G : ℝ → ℝ}
    (hG : HasDirichletLatticeDecay G) :
    Tendsto (fun σ : ℝ => σ ^ 3 * G σ) atTop (𝓝 0) := by
  obtain ⟨C, σ₀, hbd⟩ := hG
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := 24 * max C 0 / Real.log 2 ^ 4
  have hzero : Tendsto (fun σ : ℝ => B * σ⁻¹) atTop (𝓝 0) := by
    simpa [mul_zero] using tendsto_inv_atTop_zero.const_mul B
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop (max σ₀ 1)] with σ hσ
  have hσ₀ : σ₀ ≤ σ := (le_max_left σ₀ 1).trans hσ
  have hσ1 : 1 ≤ σ := (le_max_right σ₀ 1).trans hσ
  have hσ_pos : 0 < σ := by linarith
  have ht_pos : 0 < Real.log 2 * σ := mul_pos hl2 hσ_pos
  have hexp_t4 : (Real.log 2 * σ) ^ 4 / 24 ≤ Real.exp (Real.log 2 * σ) := by
    have hsum := Real.sum_le_exp_of_nonneg ht_pos.le 5
    have hterm : (Real.log 2 * σ) ^ 4 / (Nat.factorial 4 : ℝ) ≤
        ∑ i ∈ Finset.range 5, (Real.log 2 * σ) ^ i / (Nat.factorial i : ℝ) := by
      refine Finset.single_le_sum (f := fun i : ℕ => (Real.log 2 * σ) ^ i / (Nat.factorial i : ℝ))
        (fun i _ => by positivity) ?_
      simp
    have hfac4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac4] at hterm
    exact hterm.trans hsum
  have h2_neg : (2 : ℝ) ^ (-σ) ≤ 24 / (Real.log 2 ^ 4 * σ ^ 4) := by
    have hrew : (2 : ℝ) ^ (-σ) = (Real.exp (Real.log 2 * σ))⁻¹ := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
      congr 1; ring
    rw [hrew, inv_eq_one_div]
    have h1 := one_div_le_one_div_of_le (by positivity) hexp_t4
    calc 1 / Real.exp (Real.log 2 * σ)
        ≤ 1 / ((Real.log 2 * σ) ^ 4 / 24) := h1
      _ = 24 / (Real.log 2 ^ 4 * σ ^ 4) := by field_simp
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hσ_pos 3)]
  have hG_le : |G σ| ≤ max C 0 * (2 : ℝ) ^ (-σ) :=
    (hbd σ hσ₀).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity))
  calc σ ^ 3 * |G σ|
      ≤ σ ^ 3 * (max C 0 * (2 : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left hG_le (by positivity)
    _ ≤ σ ^ 3 * (max C 0 * (24 / (Real.log 2 ^ 4 * σ ^ 4))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2_neg (le_max_right C 0)) (by positivity)
    _ = B * σ⁻¹ := by
        dsimp [B]
        field_simp [hσ_pos.ne', hl2.ne']

/-- Exact real-axis formula for `Re(−W_β'/W_β)(σ)` on `σ > 1/2`. -/
theorem re_neg_logDeriv_criticalSplit_real (β : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (-logDeriv (criticalSplitMultiplier β) (σ : ℂ)).re =
      2 * β ^ 2 / ((σ - 1 / 2) * ((σ - 1 / 2) ^ 2 + β ^ 2)) := by
  set u : ℝ := σ - 1 / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hs0 : (σ : ℂ) - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hnum_nz : ((σ : ℂ) - 1 / 2) ^ 2 + (β : ℂ) ^ 2 ≠ 0 := by
    have hval : ((σ : ℂ) - 1 / 2) ^ 2 + (β : ℂ) ^ 2 = ((u ^ 2 + β ^ 2 : ℝ) : ℂ) := by
      dsimp [u]; push_cast; ring
    rw [hval]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hd_num : HasDerivAt (fun w : ℂ => (w - 1 / 2) ^ 2 + (β : ℂ) ^ 2)
      (2 * ((σ : ℂ) - 1 / 2)) (σ : ℂ) :=
    ((((hasDerivAt_id (σ : ℂ)).sub_const (1 / 2 : ℂ)).pow 2).add_const
      ((β : ℂ) ^ 2)).congr_deriv (by ring)
  have hd_den : HasDerivAt (fun w : ℂ => (w - 1 / 2) ^ 2)
      (2 * ((σ : ℂ) - 1 / 2)) (σ : ℂ) :=
    (((hasDerivAt_id (σ : ℂ)).sub_const (1 / 2 : ℂ)).pow 2).congr_deriv (by ring)
  unfold criticalSplitMultiplier
  rw [logDeriv_div (f := fun w => (w - 1 / 2) ^ 2 + (β : ℂ) ^ 2)
        (g := fun w => (w - 1 / 2) ^ 2) (σ : ℂ) hnum_nz (pow_ne_zero 2 hs0)
        hd_num.differentiableAt hd_den.differentiableAt,
      logDeriv_apply, logDeriv_apply, hd_num.deriv, hd_den.deriv]
  have hcast : -(2 * ((σ : ℂ) - 1 / 2) / (((σ : ℂ) - 1 / 2) ^ 2 + (β : ℂ) ^ 2) -
      2 * ((σ : ℂ) - 1 / 2) / ((σ : ℂ) - 1 / 2) ^ 2) =
      ((2 * β ^ 2 / (u * (u ^ 2 + β ^ 2)) : ℝ) : ℂ) := by
    have huC : ((σ : ℂ) - 1 / 2) = (u : ℂ) := by dsimp [u]; push_cast; norm_num
    rw [huC]
    have huC_nz : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hqC_nz : (u : ℂ) ^ 2 + (β : ℂ) ^ 2 ≠ 0 := by
      exact_mod_cast (show u ^ 2 + β ^ 2 ≠ 0 by positivity)
    push_cast
    field_simp [huC_nz, hqC_nz]
    ring
  rw [hcast, Complex.ofReal_re]

/-- **Algebraic `Θ(σ^{-3})` Asymptotics of Outward Critical Splitting:**
`lim_{σ → +∞} σ³ Re(−W_β'/W_β)(σ) = 2 β²`. -/
theorem tendsto_cube_mul_neg_logDeriv_criticalSplit (β : ℝ) :
    Tendsto (fun σ : ℝ => σ ^ 3 * (-logDeriv (criticalSplitMultiplier β) (σ : ℂ)).re)
      atTop (𝓝 (2 * β ^ 2)) := by
  have hinv1 : Tendsto (fun σ : ℝ => (1 : ℝ) - (1 / 2 : ℝ) * σ⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul (1 / 2 : ℝ))
  have hinv2 : Tendsto (fun σ : ℝ => ((1 : ℝ) - (1 / 2 : ℝ) * σ⁻¹) ^ 2 + β ^ 2 * (σ⁻¹) ^ 2)
      atTop (𝓝 1) := by
    have h0 : Tendsto (fun σ : ℝ => β ^ 2 * (σ⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.pow 2).const_mul (β ^ 2)
    simpa using (hinv1.pow 2).add h0
  have hden : Tendsto (fun σ : ℝ =>
      (1 - (1 / 2 : ℝ) * σ⁻¹) * ((1 - (1 / 2 : ℝ) * σ⁻¹) ^ 2 + β ^ 2 * (σ⁻¹) ^ 2))
      atTop (𝓝 1) := by
    simpa using hinv1.mul hinv2
  have hrat : Tendsto (fun σ : ℝ =>
      2 * β ^ 2 / ((1 - (1 / 2 : ℝ) * σ⁻¹) * ((1 - (1 / 2 : ℝ) * σ⁻¹) ^ 2 + β ^ 2 * (σ⁻¹) ^ 2)))
      atTop (𝓝 (2 * β ^ 2)) :=
    (tendsto_const_nhds.div hden one_ne_zero).congr fun _ => rfl
  refine hrat.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  have hσ0 : σ ≠ 0 := by linarith
  rw [re_neg_logDeriv_criticalSplit_real β (by linarith)]
  have hden_eq : (σ - 1 / 2) * ((σ - 1 / 2) ^ 2 + β ^ 2) =
      σ ^ 3 * ((1 - (1 / 2 : ℝ) * σ⁻¹) * ((1 - (1 / 2 : ℝ) * σ⁻¹) ^ 2 + β ^ 2 * (σ⁻¹) ^ 2)) := by
    field_simp [hσ0]
  rw [hden_eq]
  field_simp [hσ0]

/-- Exact real-axis formula for `Re(−(coupledQuartetSymSquare b a γ)' / coupledQuartetSymSquare b a γ)(σ)`
on `σ > 1` (`|b| < 1/2`, `|a| < 1/2`). -/
theorem re_neg_logDeriv_coupledQuartetSymSquare_real {b a γ σ : ℝ}
    (hb : |b| < 1 / 2) (ha : |a| < 1 / 2) (hσ : 1 < σ) :
    (-logDeriv (coupledQuartetSymSquare b a γ) (σ : ℂ)).re =
      4 * b ^ 2 / ((σ - 1 / 2) * ((σ - 1 / 2) ^ 2 - b ^ 2)) +
      (2 * (σ - 1 / 2 - a) / ((σ - 1 / 2 - a) ^ 2 + γ ^ 2) +
       2 * (σ - 1 / 2 + a) / ((σ - 1 / 2 + a) ^ 2 + γ ^ 2) -
       4 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + γ ^ 2)) := by
  obtain ⟨hb_lo, hb_hi⟩ := abs_lt.mp hb
  obtain ⟨ha_lo, ha_hi⟩ := abs_lt.mp ha
  set u : ℝ := σ - 1 / 2
  have hu : 1 / 2 < u := by dsimp [u]; linarith
  have hub_pos : 0 < u ^ 2 - b ^ 2 := by nlinarith
  have hs0 : (σ : ℂ) - 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hP_val : realPairPoly (1 / 2 + b) (σ : ℂ) = ((u ^ 2 - b ^ 2 : ℝ) : ℂ) := by
    unfold realPairPoly; dsimp [u]; push_cast; ring
  have hP_nz : realPairPoly (1 / 2 + b) (σ : ℂ) ≠ 0 := by
    rw [hP_val]; exact Complex.ofReal_ne_zero.mpr hub_pos.ne'
  have hCrit_val : quartetCritPoly γ (σ : ℂ) = (((u ^ 2 + γ ^ 2) ^ 2 : ℝ) : ℂ) := by
    unfold quartetCritPoly; dsimp [u]; push_cast; ring
  have hCrit_nz : quartetCritPoly γ (σ : ℂ) ≠ 0 := by
    rw [hCrit_val]; exact Complex.ofReal_ne_zero.mpr (by positivity)
  let q₁ : ℂ → ℂ := fun w => (w - ((1 / 2 + a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2
  let q₂ : ℂ → ℂ := fun w => (w - ((1 / 2 - a : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2
  let q₀ : ℂ → ℂ := fun w => (w - 1 / 2) ^ 2 + (γ : ℂ) ^ 2
  have hq₁_pos : 0 < (u - a) ^ 2 + γ ^ 2 := by
    have : 0 < u - a := by linarith
    positivity
  have hq₂_pos : 0 < (u + a) ^ 2 + γ ^ 2 := by
    have : 0 < u + a := by linarith
    positivity
  have hq₀_pos : 0 < u ^ 2 + γ ^ 2 := by positivity
  have hq₁_val : q₁ (σ : ℂ) = (((u - a) ^ 2 + γ ^ 2 : ℝ) : ℂ) := by
    dsimp [q₁, u]; push_cast; ring
  have hq₂_val : q₂ (σ : ℂ) = (((u + a) ^ 2 + γ ^ 2 : ℝ) : ℂ) := by
    dsimp [q₂, u]; push_cast; ring
  have hq₀_val : q₀ (σ : ℂ) = ((u ^ 2 + γ ^ 2 : ℝ) : ℂ) := by
    dsimp [q₀, u]; push_cast; ring
  have hq₁_nz : q₁ (σ : ℂ) ≠ 0 := by rw [hq₁_val]; exact Complex.ofReal_ne_zero.mpr hq₁_pos.ne'
  have hq₂_nz : q₂ (σ : ℂ) ≠ 0 := by rw [hq₂_val]; exact Complex.ofReal_ne_zero.mpr hq₂_pos.ne'
  have hq₀_nz : q₀ (σ : ℂ) ≠ 0 := by rw [hq₀_val]; exact Complex.ofReal_ne_zero.mpr hq₀_pos.ne'
  have hd_P : HasDerivAt (realPairPoly (1 / 2 + b)) (2 * (u : ℂ)) (σ : ℂ) := by
    have heq : realPairPoly (1 / 2 + b) = fun w : ℂ => (w - 1 / 2) ^ 2 - (b : ℂ) ^ 2 := by
      funext w; unfold realPairPoly; push_cast; ring
    rw [heq]
    refine ((((hasDerivAt_id (σ : ℂ)).sub_const (1 / 2 : ℂ)).pow 2).sub_const ((b : ℂ) ^ 2)).congr_deriv ?_
    dsimp [u]; push_cast; ring
  have hd_sq : HasDerivAt (fun w : ℂ => (w - 1 / 2) ^ 2) (2 * (u : ℂ)) (σ : ℂ) := by
    refine (((hasDerivAt_id (σ : ℂ)).sub_const (1 / 2 : ℂ)).pow 2).congr_deriv ?_
    dsimp [u]; push_cast; ring
  have hd_q₁ : HasDerivAt q₁ (2 * ((u - a : ℝ) : ℂ)) (σ : ℂ) := by
    dsimp [q₁]
    refine ((((hasDerivAt_id (σ : ℂ)).sub_const _).pow 2).add_const _).congr_deriv ?_
    dsimp [u]; push_cast; ring
  have hd_q₂ : HasDerivAt q₂ (2 * ((u + a : ℝ) : ℂ)) (σ : ℂ) := by
    dsimp [q₂]
    refine ((((hasDerivAt_id (σ : ℂ)).sub_const _).pow 2).add_const _).congr_deriv ?_
    dsimp [u]; push_cast; ring
  have hd_q₀ : HasDerivAt q₀ (2 * (u : ℂ)) (σ : ℂ) := by
    dsimp [q₀]
    refine ((((hasDerivAt_id (σ : ℂ)).sub_const _).pow 2).add_const _).congr_deriv ?_
    dsimp [u]; push_cast; ring
  have hM_nz : midpointSymSquare (1 / 2 + b) (σ : ℂ) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hs0) hP_nz
  have hM_diff : DifferentiableAt ℂ (midpointSymSquare (1 / 2 + b)) (σ : ℂ) :=
    DifferentiableAt.div hd_sq.differentiableAt hd_P.differentiableAt hP_nz
  have hQ_eq : (fun w => quartetCritPoly γ w / quartetOffPoly a γ w) =
      fun w => q₀ w ^ 2 / (q₁ w * q₂ w) := by
    funext w; unfold quartetCritPoly quartetOffPoly; dsimp [q₀, q₁, q₂]
  have hQ_nz : (quartetCritPoly γ (σ : ℂ) / quartetOffPoly a γ (σ : ℂ)) ≠ 0 :=
    div_ne_zero hCrit_nz (mul_ne_zero hq₁_nz hq₂_nz)
  have hQ_diff : DifferentiableAt ℂ (fun w => quartetCritPoly γ w / quartetOffPoly a γ w) (σ : ℂ) := by
    rw [hQ_eq]
    exact DifferentiableAt.div (hd_q₀.differentiableAt.fun_pow 2)
      (hd_q₁.differentiableAt.mul hd_q₂.differentiableAt) (mul_ne_zero hq₁_nz hq₂_nz)
  unfold coupledQuartetSymSquare
  rw [logDeriv_mul (f := fun w => midpointSymSquare (1 / 2 + b) w ^ 2)
        (g := fun w => quartetCritPoly γ w / quartetOffPoly a γ w) (σ : ℂ)
        (pow_ne_zero 2 hM_nz) hQ_nz (hM_diff.fun_pow 2) hQ_diff,
      logDeriv_fun_pow hM_diff 2]
  have hld_M : logDeriv (midpointSymSquare (1 / 2 + b)) (σ : ℂ) =
      (((-2 * b ^ 2 / (u * (u ^ 2 - b ^ 2)) : ℝ)) : ℂ) := by
    unfold midpointSymSquare
    rw [logDeriv_div (f := fun w => (w - 1 / 2) ^ 2) (g := realPairPoly (1 / 2 + b)) (σ : ℂ)
          (pow_ne_zero 2 hs0) hP_nz hd_sq.differentiableAt hd_P.differentiableAt,
        logDeriv_apply, logDeriv_apply, hd_sq.deriv, hd_P.deriv, hP_val]
    have hs_sq : ((σ : ℂ) - 1 / 2) ^ 2 = ((u ^ 2 : ℝ) : ℂ) := by dsimp [u]; push_cast; ring
    rw [hs_sq]
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hubC : (u : ℂ) ^ 2 - (b : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hub_pos.ne'
    push_cast
    field_simp [huC, hubC]
    ring
  have hld_Q : logDeriv (fun w => quartetCritPoly γ w / quartetOffPoly a γ w) (σ : ℂ) =
      (((4 * u / (u ^ 2 + γ ^ 2) - 2 * (u - a) / ((u - a) ^ 2 + γ ^ 2) -
          2 * (u + a) / ((u + a) ^ 2 + γ ^ 2) : ℝ)) : ℂ) := by
    rw [hQ_eq,
        logDeriv_div (f := fun w => q₀ w ^ 2) (g := fun w => q₁ w * q₂ w) (σ : ℂ)
          (pow_ne_zero 2 hq₀_nz) (mul_ne_zero hq₁_nz hq₂_nz)
          (hd_q₀.differentiableAt.fun_pow 2) (hd_q₁.differentiableAt.mul hd_q₂.differentiableAt),
        logDeriv_fun_pow hd_q₀.differentiableAt 2,
        logDeriv_mul (f := q₁) (g := q₂) (σ : ℂ) hq₁_nz hq₂_nz
          hd_q₁.differentiableAt hd_q₂.differentiableAt,
        logDeriv_apply, logDeriv_apply, logDeriv_apply,
        hd_q₀.deriv, hd_q₁.deriv, hd_q₂.deriv, hq₀_val, hq₁_val, hq₂_val]
    push_cast
    ring
  rw [hld_M, hld_Q]
  have htot : -((2 : ℕ) * (((-2 * b ^ 2 / (u * (u ^ 2 - b ^ 2)) : ℝ)) : ℂ) +
      (((4 * u / (u ^ 2 + γ ^ 2) - 2 * (u - a) / ((u - a) ^ 2 + γ ^ 2) -
          2 * (u + a) / ((u + a) ^ 2 + γ ^ 2) : ℝ)) : ℂ)) =
      (((4 * b ^ 2 / (u * (u ^ 2 - b ^ 2)) +
          (2 * (u - a) / ((u - a) ^ 2 + γ ^ 2) +
           2 * (u + a) / ((u + a) ^ 2 + γ ^ 2) -
           4 * u / (u ^ 2 + γ ^ 2)) : ℝ)) : ℂ) := by
    push_cast; ring
  rw [htot, Complex.ofReal_re]

/-- **Algebraic `Θ(σ^{-3})` Asymptotics of Quartet Contraction (`coupledQuartetSymSquare`):**
For `|b| < 1/2` and `|a| < 1/2`,
`lim_{σ → +∞} σ³ Re(−(coupledQuartetSymSquare b a γ)' / coupledQuartetSymSquare b a γ)(σ) = 4 b² + 4 a²`. -/
theorem tendsto_cube_mul_neg_logDeriv_coupledQuartetSymSquare {b a : ℝ} (γ : ℝ)
    (hb : |b| < 1 / 2) (ha : |a| < 1 / 2) :
    Tendsto (fun σ : ℝ => σ ^ 3 * (-logDeriv (coupledQuartetSymSquare b a γ) (σ : ℂ)).re)
      atTop (𝓝 (4 * b ^ 2 + 4 * a ^ 2)) := by
  have ht0 : Tendsto (fun σ : ℝ => σ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  let uHat : ℝ → ℝ := fun t => 1 - (1 / 2 : ℝ) * t
  have huHat : Tendsto (fun σ : ℝ => uHat σ⁻¹) atTop (𝓝 1) := by
    dsimp [uHat]; simpa using tendsto_const_nhds.sub (ht0.const_mul (1 / 2 : ℝ))
  have hterm1 : Tendsto (fun σ : ℝ =>
      4 * b ^ 2 / (uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - b ^ 2 * (σ⁻¹) ^ 2)))
      atTop (𝓝 (4 * b ^ 2)) := by
    have hden : Tendsto (fun σ : ℝ => uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - b ^ 2 * (σ⁻¹) ^ 2))
        atTop (𝓝 1) := by
      have h0 : Tendsto (fun σ : ℝ => b ^ 2 * (σ⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using (ht0.pow 2).const_mul (b ^ 2)
      simpa using huHat.mul ((huHat.pow 2).sub h0)
    exact (tendsto_const_nhds.div hden one_ne_zero).congr fun _ => rfl
  have hterm2 : Tendsto (fun σ : ℝ =>
      4 * a ^ 2 * uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - (a ^ 2 + 3 * γ ^ 2) * (σ⁻¹) ^ 2) /
        (((uHat σ⁻¹ - a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
         ((uHat σ⁻¹ + a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
         (uHat σ⁻¹ ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)))
      atTop (𝓝 (4 * a ^ 2)) := by
    have hnum : Tendsto (fun σ : ℝ =>
        4 * a ^ 2 * uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - (a ^ 2 + 3 * γ ^ 2) * (σ⁻¹) ^ 2))
        atTop (𝓝 (4 * a ^ 2)) := by
      have h0 : Tendsto (fun σ : ℝ => (a ^ 2 + 3 * γ ^ 2) * (σ⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using (ht0.pow 2).const_mul (a ^ 2 + 3 * γ ^ 2)
      simpa using (huHat.const_mul (4 * a ^ 2)).mul ((huHat.pow 2).sub h0)
    have hd1 : Tendsto (fun σ : ℝ => (uHat σ⁻¹ - a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)
        atTop (𝓝 1) := by
      have ha0 : Tendsto (fun σ : ℝ => a * σ⁻¹) atTop (𝓝 0) := by simpa using ht0.const_mul a
      have hg0 : Tendsto (fun σ : ℝ => γ ^ 2 * (σ⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using (ht0.pow 2).const_mul (γ ^ 2)
      simpa using ((huHat.sub ha0).pow 2).add hg0
    have hd2 : Tendsto (fun σ : ℝ => (uHat σ⁻¹ + a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)
        atTop (𝓝 1) := by
      have ha0 : Tendsto (fun σ : ℝ => a * σ⁻¹) atTop (𝓝 0) := by simpa using ht0.const_mul a
      have hg0 : Tendsto (fun σ : ℝ => γ ^ 2 * (σ⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using (ht0.pow 2).const_mul (γ ^ 2)
      simpa using ((huHat.add ha0).pow 2).add hg0
    have hd3 : Tendsto (fun σ : ℝ => uHat σ⁻¹ ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)
        atTop (𝓝 1) := by
      have hg0 : Tendsto (fun σ : ℝ => γ ^ 2 * (σ⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using (ht0.pow 2).const_mul (γ ^ 2)
      simpa using (huHat.pow 2).add hg0
    have hden : Tendsto (fun σ : ℝ =>
        ((uHat σ⁻¹ - a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
        ((uHat σ⁻¹ + a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
        (uHat σ⁻¹ ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)) atTop (𝓝 1) := by
      simpa using (hd1.mul hd2).mul hd3
    exact (hnum.div hden one_ne_zero).congr fun _ => rfl
  refine (hterm1.add hterm2).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
  obtain ⟨hb_lo, hb_hi⟩ := abs_lt.mp hb
  obtain ⟨ha_lo, ha_hi⟩ := abs_lt.mp ha
  have hσ0 : σ ≠ 0 := by linarith
  have hu_eq : σ - 1 / 2 = σ * uHat σ⁻¹ := by
    dsimp [uHat]; field_simp [hσ0]
  have hq1_nz : (σ - 1 / 2 - a) ^ 2 + γ ^ 2 ≠ 0 := by
    have : 0 < σ - 1 / 2 - a := by linarith
    positivity
  have hq2_nz : (σ - 1 / 2 + a) ^ 2 + γ ^ 2 ≠ 0 := by
    have : 0 < σ - 1 / 2 + a := by linarith
    positivity
  have hq0_nz : (σ - 1 / 2) ^ 2 + γ ^ 2 ≠ 0 := by
    have : 0 < σ - 1 / 2 := by linarith
    positivity
  have ht1_eq : σ ^ 3 * (4 * b ^ 2 / ((σ - 1 / 2) * ((σ - 1 / 2) ^ 2 - b ^ 2))) =
      4 * b ^ 2 / (uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - b ^ 2 * (σ⁻¹) ^ 2)) := by
    have hd_eq : (σ - 1 / 2) * ((σ - 1 / 2) ^ 2 - b ^ 2) =
        σ ^ 3 * (uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - b ^ 2 * (σ⁻¹) ^ 2)) := by
      rw [hu_eq]; field_simp [hσ0]
    rw [hd_eq]
    field_simp [hσ0]
  have ht2_eq : σ ^ 3 *
      (2 * (σ - 1 / 2 - a) / ((σ - 1 / 2 - a) ^ 2 + γ ^ 2) +
       2 * (σ - 1 / 2 + a) / ((σ - 1 / 2 + a) ^ 2 + γ ^ 2) -
       4 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + γ ^ 2)) =
      4 * a ^ 2 * uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - (a ^ 2 + 3 * γ ^ 2) * (σ⁻¹) ^ 2) /
        (((uHat σ⁻¹ - a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
         ((uHat σ⁻¹ + a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
         (uHat σ⁻¹ ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)) := by
    have hrat_q : 2 * (σ - 1 / 2 - a) / ((σ - 1 / 2 - a) ^ 2 + γ ^ 2) +
        2 * (σ - 1 / 2 + a) / ((σ - 1 / 2 + a) ^ 2 + γ ^ 2) -
        4 * (σ - 1 / 2) / ((σ - 1 / 2) ^ 2 + γ ^ 2) =
        4 * a ^ 2 * (σ - 1 / 2) * ((σ - 1 / 2) ^ 2 - (a ^ 2 + 3 * γ ^ 2)) /
          (((σ - 1 / 2 - a) ^ 2 + γ ^ 2) *
           ((σ - 1 / 2 + a) ^ 2 + γ ^ 2) *
           ((σ - 1 / 2) ^ 2 + γ ^ 2)) := by
      field_simp [hq1_nz, hq2_nz, hq0_nz]
      ring
    have hnum_eq : σ ^ 3 * (4 * a ^ 2 * (σ - 1 / 2) * ((σ - 1 / 2) ^ 2 - (a ^ 2 + 3 * γ ^ 2))) =
        σ ^ 6 * (4 * a ^ 2 * uHat σ⁻¹ * (uHat σ⁻¹ ^ 2 - (a ^ 2 + 3 * γ ^ 2) * (σ⁻¹) ^ 2)) := by
      rw [hu_eq]; field_simp [hσ0]
    have hden_eq :
        ((σ - 1 / 2 - a) ^ 2 + γ ^ 2) *
        ((σ - 1 / 2 + a) ^ 2 + γ ^ 2) *
        ((σ - 1 / 2) ^ 2 + γ ^ 2) =
        σ ^ 6 * (((uHat σ⁻¹ - a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
                 ((uHat σ⁻¹ + a * σ⁻¹) ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2) *
                 (uHat σ⁻¹ ^ 2 + γ ^ 2 * (σ⁻¹) ^ 2)) := by
      rw [hu_eq]; field_simp [hσ0]
    rw [hrat_q, mul_div_assoc', hnum_eq, hden_eq]
    field_simp [hσ0]
  symm
  rw [re_neg_logDeriv_coupledQuartetSymSquare_real hb ha hσ, mul_add, ht1_eq, ht2_eq]

/-- **Hadamard Surgery Escapes the Discrete Dirichlet Log-Lattice (`criticalSplit_escapes_dirichletLattice`).**
If `F` is holomorphic and nonvanishing on `Re s > 1` with `O(2^{-σ})` Dirichlet log-lattice decay
on the real axis, then for every `β ≠ 0`, `F · W_β` **cannot** have `O(2^{-σ})` Dirichlet
log-lattice decay! -/
theorem criticalSplit_escapes_dirichletLattice {F : ℂ → ℂ} {β : ℝ} (hβ : β ≠ 0)
    (hdiff : DifferentiableOn ℂ F {s : ℂ | 1 < s.re})
    (hnz : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hF_lat : HasDirichletLatticeDecay (fun σ : ℝ => (-logDeriv F (σ : ℂ)).re)) :
    ¬ HasDirichletLatticeDecay
      (fun σ : ℝ => (-logDeriv (fun s => F s * criticalSplitMultiplier β s) (σ : ℂ)).re) := by
  intro hprod_lat
  have hlimF := tendsto_cube_mul_zero_of_dirichletLatticeDecay hF_lat
  have hlimP := tendsto_cube_mul_zero_of_dirichletLatticeDecay hprod_lat
  have hlimW := tendsto_cube_mul_neg_logDeriv_criticalSplit β
  have hsum : Tendsto
      (fun σ : ℝ => σ ^ 3 * (-logDeriv F (σ : ℂ)).re +
        σ ^ 3 * (-logDeriv (criticalSplitMultiplier β) (σ : ℂ)).re)
      atTop (𝓝 (2 * β ^ 2)) := by
    simpa using hlimF.add hlimW
  have heq : (fun σ : ℝ => σ ^ 3 * (-logDeriv F (σ : ℂ)).re +
        σ ^ 3 * (-logDeriv (criticalSplitMultiplier β) (σ : ℂ)).re) =ᶠ[atTop]
      fun σ : ℝ => σ ^ 3 * (-logDeriv (fun s => F s * criticalSplitMultiplier β s) (σ : ℂ)).re := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
    have hs : 1 < ((σ : ℂ)).re := by simp; exact hσ
    have hs_half : (σ : ℂ) - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hW_nz : criticalSplitMultiplier β (σ : ℂ) ≠ 0 := by
      unfold criticalSplitMultiplier
      have hnum : ((σ : ℂ) - 1 / 2) ^ 2 + (β : ℂ) ^ 2 =
          ((((σ - 1 / 2) ^ 2 + β ^ 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [hnum]
      exact div_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (pow_ne_zero 2 hs_half)
    have hW_diff : DifferentiableAt ℂ (criticalSplitMultiplier β) (σ : ℂ) := by
      unfold criticalSplitMultiplier
      exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero 2 hs_half)
    rw [logDeriv_mul (f := F) (g := criticalSplitMultiplier β) (σ : ℂ)
          (hnz _ hs) hW_nz ((hdiff _ hs).differentiableAt (hopen.mem_nhds hs)) hW_diff,
        neg_add, Complex.add_re, mul_add]
  have h2b0 : 2 * β ^ 2 = 0 := tendsto_nhds_unique (hsum.congr' heq) hlimP
  have hpos : 0 < 2 * β ^ 2 := by positivity
  linarith

/-- **Quartet Contraction Escapes the Discrete Dirichlet Log-Lattice (`coupledQuartet_escapes_dirichletLattice`).**
If `F` has `O(2^{-σ})` Dirichlet log-lattice decay on `Re s > 1`, then for every `0 < a < 1/2`,
`|b| < 1/2`, and `γ ∈ ℝ`, `F · coupledQuartetSymSquare b a γ` **cannot** have `O(2^{-σ})`
Dirichlet log-lattice decay! -/
theorem coupledQuartet_escapes_dirichletLattice {F : ℂ → ℂ} {b a γ : ℝ}
    (hb : |b| < 1 / 2) (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (hdiff : DifferentiableOn ℂ F {s : ℂ | 1 < s.re})
    (hnz : ∀ s : ℂ, 1 < s.re → F s ≠ 0)
    (hF_lat : HasDirichletLatticeDecay (fun σ : ℝ => (-logDeriv F (σ : ℂ)).re)) :
    ¬ HasDirichletLatticeDecay
      (fun σ : ℝ =>
        (-logDeriv (fun s => F s * coupledQuartetSymSquare b a γ s) (σ : ℂ)).re) := by
  intro hprod_lat
  have ha_abs : |a| < 1 / 2 := abs_lt.mpr ⟨by linarith, ha1⟩
  have hlimF := tendsto_cube_mul_zero_of_dirichletLatticeDecay hF_lat
  have hlimP := tendsto_cube_mul_zero_of_dirichletLatticeDecay hprod_lat
  have hlimW := tendsto_cube_mul_neg_logDeriv_coupledQuartetSymSquare γ hb ha_abs
  have hsum : Tendsto
      (fun σ : ℝ => σ ^ 3 * (-logDeriv F (σ : ℂ)).re +
        σ ^ 3 * (-logDeriv (coupledQuartetSymSquare b a γ) (σ : ℂ)).re)
      atTop (𝓝 (4 * b ^ 2 + 4 * a ^ 2)) := by
    simpa using hlimF.add hlimW
  have heq : (fun σ : ℝ => σ ^ 3 * (-logDeriv F (σ : ℂ)).re +
        σ ^ 3 * (-logDeriv (coupledQuartetSymSquare b a γ) (σ : ℂ)).re) =ᶠ[atTop]
      fun σ : ℝ =>
        σ ^ 3 * (-logDeriv (fun s => F s * coupledQuartetSymSquare b a γ s) (σ : ℂ)).re := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    obtain ⟨hb_lo, hb_hi⟩ := abs_lt.mp hb
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
    have hs : 1 < ((σ : ℂ)).re := by simp; exact hσ
    have hs_half : (σ : ℂ) - 1 / 2 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hP_nz : realPairPoly (1 / 2 + b) (σ : ℂ) ≠ 0 := by
      unfold realPairPoly
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    have hOff_nz : quartetOffPoly a γ (σ : ℂ) ≠ 0 := by
      unfold quartetOffPoly
      rw [sq_add_sq_factor (σ : ℂ) (1 / 2 + a) γ, sq_add_sq_factor (σ : ℂ) (1 / 2 - a) γ]
      refine mul_ne_zero (mul_ne_zero (fun h => ?_) (fun h => ?_))
        (mul_ne_zero (fun h => ?_) (fun h => ?_)) <;>
        (have := congrArg Complex.re h; simp at this; linarith)
    have hCrit_nz : quartetCritPoly γ (σ : ℂ) ≠ 0 := by
      unfold quartetCritPoly
      have hf := sq_add_sq_factor (σ : ℂ) (1 / 2) γ
      have hc : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
      rw [hc] at hf; rw [hf]
      refine pow_ne_zero 2 (mul_ne_zero (fun h => ?_) (fun h => ?_)) <;>
        (have := congrArg Complex.re h; simp at this; linarith)
    have hW_nz : coupledQuartetSymSquare b a γ (σ : ℂ) ≠ 0 := by
      unfold coupledQuartetSymSquare midpointSymSquare
      exact mul_ne_zero (pow_ne_zero 2 (div_ne_zero (pow_ne_zero 2 hs_half) hP_nz))
        (div_ne_zero hCrit_nz hOff_nz)
    have hW_diff : DifferentiableAt ℂ (coupledQuartetSymSquare b a γ) (σ : ℂ) := by
      unfold coupledQuartetSymSquare midpointSymSquare
      exact (((DifferentiableAt.div (by fun_prop) (by unfold realPairPoly; fun_prop)
        hP_nz).fun_pow 2).mul
        (DifferentiableAt.div (by unfold quartetCritPoly; fun_prop)
          (by unfold quartetOffPoly; fun_prop) hOff_nz))
    rw [logDeriv_mul (f := F) (g := coupledQuartetSymSquare b a γ) (σ : ℂ)
          (hnz _ hs) hW_nz ((hdiff _ hs).differentiableAt (hopen.mem_nhds hs)) hW_diff,
        neg_add, Complex.add_re, mul_add]
  have h0 : 4 * b ^ 2 + 4 * a ^ 2 = 0 := tendsto_nhds_unique (hsum.congr' heq) hlimP
  have hpos : 0 < 4 * b ^ 2 + 4 * a ^ 2 := by positivity
  linarith

/-! ## §6. The Positive Survivor: `CentralVanishingCeiling γ` excludes off-line zeros -/

/-- Outward `W_β` deformations at critical zeros satisfy `ord_{1/2}(Λ_β) < ord_{1/2}(Λ_γ)`:
they **strictly obey** `CentralVanishingCeiling γ` despite refuting `CoupledRigid γ`. -/
theorem criticalSplit_strictly_below_centralCeiling {γ β : ℝ}
    (hxi : RHTower.xi (1 / 2 + (γ : ℂ) * I) = 0) (hβ : β ≠ 0) :
    ∃ Λβ : ℂ → ℂ,
      HeightCoupledSystem 2 1 1 γ
        (fun s => heightCoupledF riemannZeta γ s * criticalSplitMultiplier β s) Λβ ∧
      (analyticOrderAt Λβ (1 / 2)).toNat <
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat := by
  obtain ⟨Λβ, hHCβ, hord, -⟩ := exists_criticalSplit_deformation_of_xi_zero hxi hβ
  exact ⟨Λβ, hHCβ, by omega⟩

/-- Two-sided `CoupledRigid γ` implies the one-sided `CentralVanishingCeiling γ`, while the
converse fails unconditionally at infinitely many Hardy ordinates. -/
theorem coupledRigid_implies_centralVanishingCeiling {γ : ℝ} (hrig : CoupledRigid γ) :
    CentralVanishingCeiling γ := by
  intro F Λ hHC
  obtain ⟨K, hK0, hK⟩ := hrig F Λ hHC
  have hHC0 := zeta_mem_heightCoupledSystem γ
  set Λγ := heightCoupledΛ (fun s => 2 * RHTower.xi s) γ
  have hagree : ∀ s : ℂ, 1 < s.re → Λ s = (K : ℂ) * Λγ s := by
    intro s hs
    rw [hHC.completed_eq s hs, hHC0.completed_eq s hs, hK s hs]
    ring
  have heq : EqOn Λ (fun s => (K : ℂ) * Λγ s) univ := by
    have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact hHC.analyticOnNhd_univ.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_const.mul hHC0.analyticOnNhd_univ)
      isPreconnected_univ (mem_univ (2 : ℂ))
      (Filter.eventually_of_mem (hU.mem_nhds (by norm_num)) fun s hs => hagree s hs)
  have hfun : Λ = fun s => (K : ℂ) * Λγ s := funext fun s => heq (mem_univ s)
  have hconst : analyticOrderAt (fun _ : ℂ => (K : ℂ)) (1 / 2 : ℂ) = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by exact_mod_cast hK0)
  have hordK : analyticOrderAt Λ (1 / 2) = analyticOrderAt Λγ (1 / 2) := by
    rw [hfun, show (fun s => (K : ℂ) * Λγ s) = (fun _ : ℂ => (K : ℂ)) * Λγ from rfl,
      analyticOrderAt_mul analyticAt_const (hHC0.entire_Λ.analyticAt _), hconst, zero_add]
  rw [hordK]

/-- **The one-sided `CentralVanishingCeiling γ` excludes every off-line zero at ordinate `γ`.** -/
theorem xi_ne_zero_of_centralVanishingCeiling {γ a : ℝ}
    (hceil : CentralVanishingCeiling γ) (hγ : γ ≠ 0) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    RHTower.xi (1 / 2 + a + γ * I) ≠ 0 := by
  intro hxi
  have hZ := completedPositiveSystem_riemannZeta
  have hq : (fun s => 2 * RHTower.xi s) (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 := by
    simp only [hxi, mul_zero]
  obtain ⟨Λc, hHCc, hord⟩ :=
    CompletedPositiveSystem.contractComplexQuartet_heightCoupled hZ ha0 ha1 hγ hq
  have hle := hceil _ _ hHCc
  have h0 := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hZ γ (1 / 2)
  have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at h0
  omega

/-- **The Chiral Central-Ceiling Criterion for RH (`riemannHypothesis_of_forall_centralVanishingCeiling`).**
Unlike `∀ γ ≠ 0, CoupledRigid γ` (which is unconditionally false), the surviving one-sided ceiling
`∀ γ ≠ 0, CentralVanishingCeiling γ` accommodates all outward critical-line splittings `W_β` while
still unconditionally implying `RiemannHypothesis`. -/
theorem riemannHypothesis_of_forall_centralVanishingCeiling
    (h : ∀ γ : ℝ, γ ≠ 0 → CentralVanishingCeiling γ) :
    RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  intro s hs1 hs2 hz
  have him : s.im ≠ 0 := zeta_strip_zero_im_ne_zero hz (by linarith) hs2
  have hs : s = 1 / 2 + ((s.re - 1 / 2 : ℝ) : ℂ) + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have hne1 : s ≠ 1 := by
    intro h1; rw [h1] at hs2; simp at hs2
  have hxi : RHTower.xi s = 0 :=
    (RHTower.xi_eq_zero_iff_riemannZeta_of_re_pos (by linarith) hne1).mpr hz
  rw [hs] at hxi
  exact xi_ne_zero_of_centralVanishingCeiling (h _ him) him (by linarith) (by linarith) hxi

end GaloisForLFunctions.BiarithmeticGaugeGeometry
