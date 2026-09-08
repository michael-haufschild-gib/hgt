import GaloisForLFunctions.HTGeometry.FokasLenellsRegularizedData
import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import GaloisForLFunctions.RHTower.FokasLenellsCauchyResolvent

/-!
# A Cauchy resolvent driven by genuine Fokas–Lenells scattering data

The direct scattering construction supplies the regularized jump coefficients
of arXiv:2607.19649v1, equations (3.32)–(3.35), with their prescribed time
phases. The corpus's bounded measurable multipliers and signed Hardy
projection implement the two-channel Cauchy equation on the Sonin L² carrier.
Its norm is at most four ninths, so the inverse-equation mechanism behind
Propositions 4.3–4.4 gives unique solvability and inverse norm at most nine
fifths for every L² forcing, every position and every prescribed time.

Unlike the earlier Schwartz-symbol resolvent, these coefficients arise from
the potential through constructed spectral solutions and endpoint limits.
All smallness is discharged by the explicit normalization of an arbitrary
Schwartz potential. Nonlinear reconstruction and the claim that the specific
Riemann–Hilbert forcing lies in L² remain separate analytic steps.
-/

open MeasureTheory Complex
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The symbols are the actual regularized scattering quotients of the explicitly rescaled potential. -/
def directSymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  if reverse then regularJumpReverseReflection (globalSmallScatteringPotential q) t x z
    else regularJumpReflection (globalSmallScatteringPotential q) t x z

theorem directSymbol_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (directSymbol q t x reverse) := by
  cases reverse
  · exact (measurable_globalSmall_regularJump q t x).1
  · exact (measurable_globalSmall_regularJump q t x).2

theorem directSymbol_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖directSymbol q t x reverse z‖ ≤ 1/3 := by
  cases reverse
  · exact (globalSmall_regularJump_bounds q t x z).1
  · exact (globalSmall_regularJump_bounds q t x z).2

def directMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := volume) (directSymbol_measurable q t x reverse)
    (by positivity : (0:ℝ) ≤ 1/3) (directSymbol_bound q t x reverse)

/-- The continuous operator multiplies by the actual scattering symbol almost everywhere. -/
theorem directMultiplier_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    (directMultiplier q t x reverse u : ℝ → ℂ) =ᵐ[volume]
      (fun z => directSymbol q t x reverse z*(u : ℝ → ℂ) z) :=
  lpBoundedMulCLM_coeFn (directSymbol_measurable q t x reverse)
    (by positivity : (0:ℝ) ≤ 1/3) (directSymbol_bound q t x reverse) u

theorem directMultiplier_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (u : SoninL2) :
    ‖directMultiplier q t x reverse u‖ ≤ (1/3 : ℝ)*‖u‖ := by
  exact ((directMultiplier q t x reverse).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (norm_lpBoundedMulCLM_le
      (directSymbol_measurable q t x reverse) (by positivity : (0:ℝ) ≤ 1/3)
      (directSymbol_bound q t x reverse)) (norm_nonneg u))

/-- Right multiplication by `R` from the paper's regularized jump `I+R`. -/
def directJumpPerturbation (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  ((-directMultiplier q t x false).comp (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)).prod
    (((directMultiplier q t x true).comp (ContinuousLinearMap.fst ℂ SoninL2 SoninL2)) -
      (((directMultiplier q t x false).comp (directMultiplier q t x true)).comp
        (ContinuousLinearMap.snd ℂ SoninL2 SoninL2)))

/-- The implemented operator has the pointwise two-channel jump action. -/
theorem directJumpPerturbation_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    (fun z => (((directJumpPerturbation q t x u).1 : ℝ → ℂ) z,
      ((directJumpPerturbation q t x u).2 : ℝ → ℂ) z)) =ᵐ[volume]
      (fun z => (-directSymbol q t x false z*(u.2 : ℝ → ℂ) z,
        directSymbol q t x true z*(u.1 : ℝ → ℂ) z-
          directSymbol q t x false z*(directSymbol q t x true z*(u.2 : ℝ → ℂ) z))) := by
  change (fun z => ((-(directMultiplier q t x false u.2) : SoninL2) z,
    (directMultiplier q t x true u.1-directMultiplier q t x false (directMultiplier q t x true u.2) : SoninL2) z)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_neg (directMultiplier q t x false u.2),
    Lp.coeFn_sub (directMultiplier q t x true u.1) (directMultiplier q t x false (directMultiplier q t x true u.2)),
    directMultiplier_ae q t x false u.2, directMultiplier_ae q t x true u.1,
    directMultiplier_ae q t x false (directMultiplier q t x true u.2), directMultiplier_ae q t x true u.2]
    with z hn hs ha hb hab hbu
  simp only [hn, hs, ha, hb, hab, hbu, Pi.neg_apply, Pi.sub_apply, neg_mul]

/-- The product norm gives `1/3 + (1/3)² = 4/9`, uniformly in the input potential and time. -/
theorem directJumpPerturbation_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directJumpPerturbation q t x u‖ ≤ (4/9 : ℝ)*‖u‖ := by
  change max ‖-(directMultiplier q t x false u.2)‖
    ‖directMultiplier q t x true u.1-directMultiplier q t x false (directMultiplier q t x true u.2)‖ ≤ _
  rw [max_le_iff, norm_neg]
  have h1 := directMultiplier_bound q t x false u.2
  have h2 := directMultiplier_bound q t x true u.1
  have h3 := directMultiplier_bound q t x false (directMultiplier q t x true u.2)
  have h4 := directMultiplier_bound q t x true u.2
  have hf := norm_fst_le u
  have hs := norm_snd_le u
  constructor
  · nlinarith [norm_nonneg u]
  · have ht := norm_sub_le (directMultiplier q t x true u.1)
      (directMultiplier q t x false (directMultiplier q t x true u.2))
    nlinarith

/-- The signed Hardy projection compresses the genuine regularized jump operator. -/
def directCauchyOperator (q : SchwartzMap ℝ ℂ) (t x : ℝ) : Boundary →L[ℂ] Boundary :=
  (negativeCauchy.prodMap negativeCauchy).comp (directJumpPerturbation q t x)

theorem directCauchyOperator_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (u : Boundary) :
    ‖directCauchyOperator q t x u‖ ≤ (4/9 : ℝ)*‖u‖ := by
  apply le_trans _ (directJumpPerturbation_bound q t x u)
  change max ‖negativeCauchy (directJumpPerturbation q t x u).1‖
    ‖negativeCauchy (directJumpPerturbation q t x u).2‖ ≤
      max ‖(directJumpPerturbation q t x u).1‖ ‖(directJumpPerturbation q t x u).2‖
  exact max_le_max (negativeCauchy_bound _) (negativeCauchy_bound _)

theorem norm_directCauchyOperator_lt_one (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyOperator q t x‖ < 1 := by
  have hb := (directCauchyOperator q t x).opNorm_le_bound (by positivity : (0:ℝ) ≤ 4/9)
    (directCauchyOperator_bound q t x)
  linarith

def directResolventUnit (q : SchwartzMap ℝ ℂ) (t x : ℝ) : (Boundary →L[ℂ] Boundary)ˣ :=
  Units.oneSub (directCauchyOperator q t x) (norm_directCauchyOperator_lt_one q t x)

def directSolution (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) : Boundary :=
  ((directResolventUnit q t x)⁻¹ : (Boundary →L[ℂ] Boundary)ˣ).val d

/-- The Cauchy equation is solved with scattering data generated from the potential. -/
theorem directSolution_equation (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    directSolution q t x d-directCauchyOperator q t x (directSolution q t x d) = d := by
  have he := DFunLike.congr_fun (directResolventUnit q t x).val_inv d
  simpa [directResolventUnit, Units.val_oneSub, directSolution, mul_apply_eq_comp, sub_apply] using he

/-- The inverse norm is at most `9/5`, for all potentials after explicit rescaling and every time. -/
theorem directSolution_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    ‖directSolution q t x d‖ ≤ (9/5 : ℝ)*‖d‖ := by
  have he := (sub_eq_iff_eq_add).mp (directSolution_equation q t x d)
  have hn : ‖directSolution q t x d‖ ≤ ‖d‖+‖directCauchyOperator q t x (directSolution q t x d)‖ := by
    calc
      _ = ‖d+directCauchyOperator q t x (directSolution q t x d)‖ := congrArg norm he
      _ ≤ _ := norm_add_le _ _
  have hb := directCauchyOperator_bound q t x (directSolution q t x d)
  linarith

/-- Unique solvability of the regularized two-channel Cauchy equation with actual direct-scattering data. -/
theorem directSolution_existsUnique (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d : Boundary) :
    ∃! u : Boundary, u-directCauchyOperator q t x u = d := by
  refine ⟨directSolution q t x d,directSolution_equation q t x d,?_⟩
  intro u hu
  have he : u-directSolution q t x d = directCauchyOperator q t x (u-directSolution q t x d) := by
    rw [map_sub]
    have h1 := (sub_eq_iff_eq_add).mp hu
    have h2 := (sub_eq_iff_eq_add).mp (directSolution_equation q t x d)
    calc
      _ = (d+directCauchyOperator q t x u)-(d+directCauchyOperator q t x (directSolution q t x d)) :=
        congrArg₂ (·-·) h1 h2
      _ = _ := by abel
  have hb := directCauchyOperator_bound q t x (u-directSolution q t x d)
  rw [← he] at hb
  have hz : ‖u-directSolution q t x d‖ = 0 := by linarith [norm_nonneg (u-directSolution q t x d)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

theorem directSolution_lipschitz (q : SchwartzMap ℝ ℂ) (t x : ℝ) (d e : Boundary) :
    ‖directSolution q t x d-directSolution q t x e‖ ≤ (9/5 : ℝ)*‖d-e‖ := by
  have he : directSolution q t x (d-e) = directSolution q t x d-directSolution q t x e :=
    map_sub ((directResolventUnit q t x)⁻¹ : (Boundary →L[ℂ] Boundary)ˣ).val d e
  rw [← he]
  exact directSolution_bound q t x (d-e)

end
end RHTower.FokasLenells
