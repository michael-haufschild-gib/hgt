import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleResponse
import GaloisForLFunctions.HTGeometry.EulerQGammaDivisor
import GaloisForLFunctions.HTGeometry.EulerQGammaLanding

/-!
# The divisor of the socle ladder

In the socle variable the depth-`j` factor of the ladder is `ζ(jσ + v)`, an affine pullback of `ζ`
of slope one — unlike the dilation variable, where the slope is the depth.  The order of the
ladder at a point is therefore the finite sum of the zeta orders at the translated points, the
tail beyond the uniform depth threshold being holomorphic and zero-free.
-/

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The depth-`j` factor of the socle ladder, as a function of the socle parameter. -/
def socleFactor (σ : ℝ) (j : ℕ) (v : ℂ) : ℂ := riemannZeta ((j : ℂ) * (σ : ℂ) + v)

theorem socleFactor_eq_affine (σ : ℝ) (j : ℕ) :
    socleFactor σ j = fun v : ℂ => riemannZeta (1 * v + (j : ℂ) * (σ : ℂ)) := by
  funext v
  rw [socleFactor]
  congr 1
  ring

theorem meromorphicAt_socleFactor (σ : ℝ) (j : ℕ) (v : ℂ) :
    MeromorphicAt (socleFactor σ j) v := by
  rw [socleFactor_eq_affine]
  exact meromorphicAt_comp_affine one_ne_zero (meromorphicAt_riemannZeta _)

/-- **One depth.**  The order of the depth-`j` socle factor is the order of `ζ` at the translated
point. -/
theorem meromorphicOrderAt_socleFactor (σ : ℝ) (j : ℕ) (v : ℂ) :
    meromorphicOrderAt (socleFactor σ j) v
      = meromorphicOrderAt riemannZeta ((j : ℂ) * (σ : ℂ) + v) := by
  rw [socleFactor_eq_affine,
    meromorphicOrderAt_comp_affine one_ne_zero v (meromorphicAt_riemannZeta _)]
  congr 1
  ring

/-- The depth-truncated socle ladder. -/
def socleProduct (σ : ℝ) (J : ℕ) (v : ℂ) : ℂ :=
  ∏ j ∈ Finset.range J, socleFactor σ (j + 1) v

theorem socleProduct_eq_depthProduct (σ : ℝ) (J : ℕ) (v : ℂ) :
    socleProduct σ J v = depthProduct σ v J 0 := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [socleFactor, depthFactor_eq_zeta_depthArg, depthArg]
  norm_num

/-- **The divisor of the truncation.**  The order of the depth-truncated socle ladder is the finite
sum of the translated zeta orders. -/
theorem meromorphicOrderAt_socleProduct (σ : ℝ) (J : ℕ) (v : ℂ) :
    meromorphicOrderAt (socleProduct σ J) v
      = ∑ j ∈ Finset.range J,
        meromorphicOrderAt riemannZeta (((j + 1 : ℕ) : ℂ) * (σ : ℂ) + v) := by
  induction J with
  | zero =>
      have hone : socleProduct σ 0 = fun _ : ℂ => (1 : ℂ) := by
        funext w
        show (∏ j ∈ Finset.range 0, socleFactor σ (j + 1) w) = 1
        rw [Finset.range_zero, Finset.prod_empty]
      rw [hone, Finset.range_zero, Finset.sum_empty]
      exact meromorphicOrderAt_eq_zero_of_analytic analyticAt_const one_ne_zero
  | succ J ih =>
      have hfun : socleProduct σ (J + 1) = socleProduct σ J * socleFactor σ (J + 1) := by
        funext w
        show (∏ j ∈ Finset.range (J + 1), socleFactor σ (j + 1) w)
            = (∏ j ∈ Finset.range J, socleFactor σ (j + 1) w) * socleFactor σ (J + 1) w
        rw [Finset.prod_range_succ]
      have hmerA : MeromorphicAt (socleProduct σ J) v := by
        show MeromorphicAt (fun w : ℂ => ∏ j ∈ Finset.range J, socleFactor σ (j + 1) w) v
        exact MeromorphicAt.fun_prod fun j _ => meromorphicAt_socleFactor σ (j + 1) v
      have hmerB : MeromorphicAt (socleFactor σ (J + 1)) v := meromorphicAt_socleFactor σ (J + 1) v
      rw [hfun, meromorphicOrderAt_mul hmerA hmerB, ih,
        meromorphicOrderAt_socleFactor σ (J + 1) v, Finset.sum_range_succ]

/-- The socle tail is analytic at every point of its half-plane. -/
theorem analyticAt_tprod_zeta_socleTail {σ b : ℝ} (hσ : 0 < σ) {J : ℕ}
    (hJthr : SocleTail.socleTailThreshold σ b ≤ J) {v : ℂ} (hv : b < v.re) :
    AnalyticAt ℂ (fun w : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ w (j + J) 0)) v := by
  have hopen : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
  exact ((SocleTail.differentiableOn_tprod_zeta_socleTail hσ hJthr).analyticOnNhd hopen) v hv

/-- **(AZC.18).**  The divisor of the socle ladder is the finite sum of the zeta divisors pulled
back by the depth translations; only the depths below the uniform threshold contribute. -/
theorem meromorphicOrderAt_socleLadder {σ b : ℝ} (hσ : 0 < σ) {J : ℕ}
    (hJthr : SocleTail.socleTailThreshold σ b ≤ J) {v : ℂ} (hv : b < v.re) :
    meromorphicOrderAt (socleLadder σ) v
      = ∑ j ∈ Finset.range J,
        meromorphicOrderAt riemannZeta (((j + 1 : ℕ) : ℂ) * (σ : ℂ) + v) := by
  have hopen : IsOpen {w : ℂ | b < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hJ1 : SocleTail.socleTailThreshold σ b ≤ J + 1 := le_trans hJthr (Nat.le_succ J)
  have heq : socleLadder σ =ᶠ[nhdsWithin v {v}ᶜ]
      fun w : ℂ => socleProduct σ J w * ∏' j : ℕ, riemannZeta (depthArg σ w (j + (J + 1)) 0) := by
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hv)] with w _
    rw [socleLadder_split hσ w J, socleProduct_eq_depthProduct]
    rfl
  rw [meromorphicOrderAt_congr heq]
  have htail0 : meromorphicOrderAt
      (fun w : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ w (j + (J + 1)) 0)) v = 0 :=
    meromorphicOrderAt_eq_zero_of_analytic (analyticAt_tprod_zeta_socleTail hσ hJ1 hv)
      (SocleTail.tprod_zeta_socleTail_ne_zero hσ hJ1 (le_of_lt hv))
  have hmerA : MeromorphicAt (socleProduct σ J) v := by
    show MeromorphicAt (fun w : ℂ => ∏ j ∈ Finset.range J, socleFactor σ (j + 1) w) v
    exact MeromorphicAt.fun_prod fun j _ => meromorphicAt_socleFactor σ (j + 1) v
  have hmerB : MeromorphicAt
      (fun w : ℂ => ∏' j : ℕ, riemannZeta (depthArg σ w (j + (J + 1)) 0)) v :=
    (analyticAt_tprod_zeta_socleTail hσ hJ1 hv).meromorphicAt
  have hsplit : (fun w : ℂ =>
      socleProduct σ J w * ∏' j : ℕ, riemannZeta (depthArg σ w (j + (J + 1)) 0))
      = socleProduct σ J * fun w : ℂ =>
        ∏' j : ℕ, riemannZeta (depthArg σ w (j + (J + 1)) 0) := rfl
  rw [hsplit, meromorphicOrderAt_mul hmerA hmerB, htail0, add_zero,
    meromorphicOrderAt_socleProduct σ J v]

end

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
