import GaloisForLFunctions.RHTower.ConnesBesovProductTransfer

/-!
# Fibres of a Schwartz function on a product decay rapidly in the transverse variable

The remaining input of the `A_S` transfer (`ConnesBesovProductTransfer`) is that the constants
appearing in the one-place estimate, taken fibre by fibre, are *integrable* in the transverse
variable.  For a Schwartz function on a product that is automatic, and it is proved here.

Two facts do the work.  Restricting to a fibre is composition with the affine map
`t ↦ (t, x)`, whose linear part is an isometry onto its image, so it does not increase the norm of
any iterated derivative.  And the product norm is the maximum, so
`‖t‖^k ‖x‖^N ≤ ‖(t,x)‖^{k+N}`: one Schwartz seminorm of the ambient function controls the fibre
seminorm *and* a power of the transverse variable simultaneously.

Neither statement is in mathlib.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The inclusion of the first factor. -/
def connesFibreIncl : ℝ →L[ℝ] ℝ × X := (ContinuousLinearMap.id ℝ ℝ).prod 0

@[simp] theorem connesFibreIncl_apply (t : ℝ) : (connesFibreIncl (X := X)) t = (t, 0) := by
  rw [connesFibreIncl]
  simp

theorem connesFibreIncl_norm_le : ‖(connesFibreIncl (X := X))‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
  rw [connesFibreIncl_apply, Prod.norm_def, one_mul]
  simp

/-- **Restricting to a fibre does not increase the iterated derivatives.** -/
theorem connes_norm_iteratedFDeriv_fibre_le (η : 𝓢(ℝ × X, ℂ)) (n : ℕ) (x : X) (t : ℝ) :
    ‖iteratedFDeriv ℝ n (fun s : ℝ => η (s, x)) t‖ ≤ ‖iteratedFDeriv ℝ n η (t, x)‖ := by
  set g : ℝ × X → ℂ := fun y => η (y + (0, x)) with hg
  have hgcd : ContDiff ℝ ∞ g := by
    rw [hg]
    exact η.smooth'.comp (contDiff_id.add contDiff_const)
  have hcomp : (fun s : ℝ => η (s, x)) = g ∘ (connesFibreIncl (X := X)) := by
    funext s
    rw [hg, Function.comp_apply, connesFibreIncl_apply]
    congr 1
    simp
  have hstep := (connesFibreIncl (X := X)).iteratedFDeriv_comp_right (f := g) hgcd t
    (i := n) (by exact_mod_cast le_top)
  have hgderiv : iteratedFDeriv ℝ n g (connesFibreIncl (X := X) t)
      = iteratedFDeriv ℝ n η (t, x) := by
    rw [hg, iteratedFDeriv_comp_add_right, connesFibreIncl_apply]
    congr 1
    simp
  rw [hcomp, hstep, hgderiv]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  have hprod : (∏ _i : Fin n, ‖(connesFibreIncl (X := X))‖) ≤ 1 := by
    refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => connesFibreIncl_norm_le)
  calc ‖iteratedFDeriv ℝ n η (t, x)‖ * ∏ _i : Fin n, ‖(connesFibreIncl (X := X))‖
      ≤ ‖iteratedFDeriv ℝ n η (t, x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n η (t, x)‖ := mul_one _

/-- **The fibre seminorms decay faster than every power of the transverse variable.** -/
theorem connes_fibre_decay (η : 𝓢(ℝ × X, ℂ)) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : X) (t : ℝ),
      ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (fun s : ℝ => η (s, x)) t‖
        ≤ C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := η.decay' k n
  obtain ⟨C₁, hC₁⟩ := η.decay' (k + N) n
  have hC₀0 : 0 ≤ C₀ := le_trans (by positivity) (hC₀ 0)
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0)
  have hcoe : ∀ y : ℝ × X, (⇑η) y = η.toFun y := fun _ => rfl
  refine ⟨2 ^ N * (C₀ + C₁), by positivity, fun x t => ?_⟩
  set D : ℝ := ‖iteratedFDeriv ℝ n (fun s : ℝ => η (s, x)) t‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  have hDle : D ≤ ‖iteratedFDeriv ℝ n η (t, x)‖ :=
    connes_norm_iteratedFDeriv_fibre_le η n x t
  have hpnorm : ‖((t, x) : ℝ × X)‖ = max ‖t‖ ‖x‖ := Prod.norm_def _
  have ht : ‖t‖ ≤ ‖((t, x) : ℝ × X)‖ := by rw [hpnorm]; exact le_max_left _ _
  have hx : ‖x‖ ≤ ‖((t, x) : ℝ × X)‖ := by rw [hpnorm]; exact le_max_right _ _
  have hDnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n η (t, x)‖ := norm_nonneg _
  -- the plain bound
  have hplain : ‖t‖ ^ k * D ≤ C₀ := by
    have h : ‖((t, x) : ℝ × X)‖ ^ k * ‖iteratedFDeriv ℝ n (⇑η) (t, x)‖ ≤ C₀ := hC₀ (t, x)
    have hmono : ‖t‖ ^ k * D ≤ ‖((t, x) : ℝ × X)‖ ^ k * ‖iteratedFDeriv ℝ n η (t, x)‖ :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht k) hDle hD0 (by positivity)
    linarith
  -- the bound with a power of the transverse variable
  have hweighted : ‖x‖ ^ N * (‖t‖ ^ k * D) ≤ C₁ := by
    have h : ‖((t, x) : ℝ × X)‖ ^ (k + N) * ‖iteratedFDeriv ℝ n (⇑η) (t, x)‖ ≤ C₁ :=
      hC₁ (t, x)
    have hsplit : ‖((t, x) : ℝ × X)‖ ^ (k + N)
        = ‖((t, x) : ℝ × X)‖ ^ k * ‖((t, x) : ℝ × X)‖ ^ N := by
      rw [pow_add]
    have hmono : ‖x‖ ^ N * (‖t‖ ^ k * D)
        ≤ (‖((t, x) : ℝ × X)‖ ^ k * ‖((t, x) : ℝ × X)‖ ^ N)
          * ‖iteratedFDeriv ℝ n η (t, x)‖ := by
      have h1 : ‖t‖ ^ k * D ≤ ‖((t, x) : ℝ × X)‖ ^ k * ‖iteratedFDeriv ℝ n η (t, x)‖ :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht k) hDle hD0 (by positivity)
      have h2 : ‖x‖ ^ N ≤ ‖((t, x) : ℝ × X)‖ ^ N :=
        pow_le_pow_left₀ (norm_nonneg _) hx N
      calc ‖x‖ ^ N * (‖t‖ ^ k * D)
          ≤ ‖((t, x) : ℝ × X)‖ ^ N * (‖((t, x) : ℝ × X)‖ ^ k
              * ‖iteratedFDeriv ℝ n η (t, x)‖) :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = (‖((t, x) : ℝ × X)‖ ^ k * ‖((t, x) : ℝ × X)‖ ^ N)
              * ‖iteratedFDeriv ℝ n η (t, x)‖ := by ring
    rw [← hsplit] at hmono
    linarith
  -- combine
  have hbase : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hexp : (1 + ‖x‖) ^ (-(N : ℝ)) = ((1 + ‖x‖) ^ N)⁻¹ := by
    rw [← Real.rpow_natCast (1 + ‖x‖) N, ← Real.rpow_neg hbase.le]
  have hpow : (0 : ℝ) < (1 + ‖x‖) ^ N := by positivity
  rw [hexp, le_mul_inv_iff₀ hpow]
  have hexpand := connes_one_add_abs_pow_le N ‖x‖
  rw [abs_of_nonneg (norm_nonneg x)] at hexpand
  have hnn : (0 : ℝ) ≤ ‖t‖ ^ k * D := by positivity
  calc ‖t‖ ^ k * D * (1 + ‖x‖) ^ N
      ≤ ‖t‖ ^ k * D * (2 ^ N * (1 + ‖x‖ ^ N)) := mul_le_mul_of_nonneg_left hexpand hnn
    _ = 2 ^ N * ((‖t‖ ^ k * D) + ‖x‖ ^ N * (‖t‖ ^ k * D)) := by ring
    _ ≤ 2 ^ N * (C₀ + C₁) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The fibre constants are integrable.**  On a finite-dimensional transverse space the bound of
`connes_fibre_decay` is integrable as soon as `N` exceeds the dimension — which is exactly the
input consumed by `ConnesBesovProductTransfer.connes_fibrewise_rapidDecay`. -/
theorem connes_fibre_bound_integrable [MeasurableSpace X] [BorelSpace X]
    [FiniteDimensional ℝ X] {μ : Measure X} [μ.IsAddHaarMeasure]
    (C : ℝ) {N : ℕ} (hN : (Module.finrank ℝ X : ℝ) < (N : ℝ)) :
    Integrable (fun x : X => C * (1 + ‖x‖) ^ (-(N : ℝ))) μ :=
  (integrable_one_add_norm (E := X) (μ := μ) hN).const_mul C

end

end GaloisForLFunctions.RHTower
