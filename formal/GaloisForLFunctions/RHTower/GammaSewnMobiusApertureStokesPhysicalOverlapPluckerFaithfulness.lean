import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalOverlapPluckerSpectralOperator

/-!
# Faithfulness of the physical-overlap Pluecker spectral operator

P-G94 descends local rank-three Pluecker blocks to the shared prime-depth lattice.  This module
classifies its global zero modes.  A zero of the positive block sum must lie in every local kernel.
The reciprocal-node kernels glue along shared depth cells into one gauge coefficient, while their
canonical section is exactly the Stokes gap.  That gap grows linearly in valuation depth, so every
nonzero glued section lies outside the physical ell-two space.

Consequently the P-G94 compact positive operator is injective and has strictly positive quadratic
form on every nonzero physical vector.  Local packet nullity survives only as a non-normalizable
boundary gauge, not as a Hilbert-space eigenmode.  No coefficient or target moment is added.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace

noncomputable section
namespace RHTower.HedenmalmThetaSource


theorem gammaSewnCriticalPrimeDepthPacket_node_right_overlap (e n : ℕ) :
    gammaSewnCriticalPrimeDepthPacket_node e
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) 2 =
      gammaSewnCriticalPrimeDepthPacket_node e
        (gammaSewnCriticalAdjacentPrime_lower (n + 1))
        (gammaSewnCriticalAdjacentPrime_upper (n + 1)) 0 := by
  rfl

theorem gammaSewnCriticalPrimeDepthPacket_node_depth_overlap (e n : ℕ) :
    gammaSewnCriticalPrimeDepthPacket_node e
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) 1 =
      gammaSewnCriticalPrimeDepthPacket_node (e + 1)
        (gammaSewnCriticalAdjacentPrime_lower n)
        (gammaSewnCriticalAdjacentPrime_upper n) 0 := by
  rfl

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_depth_overlap (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, n) 1 =
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e + 1, n) 0 := by
  rfl

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_zero_eq_stokesGap (e n : ℕ) :
    gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, n) 0 =
      RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
        (gammaSewnCriticalAdjacentPrime_lower n, e) := by
  have hgap : 0 < RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
      (gammaSewnCriticalAdjacentPrime_lower n, e) :=
    RHTower.gammaSewnMobiusApertureStokesGap_pos (by norm_num) _
  simp only [gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector,
    gammaSewnCriticalPrimeDepthPacket_node,
    gammaSewnOrderedPrimeDepthPlucker_cell,
    RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode,
    RHTower.gammaSewnMobiusApertureStokesReciprocalGapNode,
    Matrix.cons_val_zero]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hgap), inv_inv]

def gammaSewnCriticalPhysicalPluckerRestriction (z : ℕ × ℕ)
    (x : GammaSewnCriticalPhysicalPluckerHilbert) : Fin 4 → ℂ :=
  fun i => inner ℂ
    (gammaSewnCriticalPhysicalPluckerBasis
      (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i)) x

theorem gammaSewnCriticalPhysicalPluckerRestriction_apply (z : ℕ × ℕ)
    (x : GammaSewnCriticalPhysicalPluckerHilbert) (i : Fin 4) :
    gammaSewnCriticalPhysicalPluckerRestriction z x i =
      x (gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel z i) := by
  simp [gammaSewnCriticalPhysicalPluckerRestriction, gammaSewnCriticalPhysicalPluckerBasis, lp.inner_single_left]

theorem gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_complexKernel (z : ℕ × ℕ) (r : Fin 4 → ℂ)
    (hr : ∀ i, ∑ j : Fin 4,
      (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z i j : ℂ) * r j = 0) :
    ∃ c : ℂ, r = fun i => c *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i := by
  let xr : Fin 4 → ℝ := fun i => (r i).re
  let xi : Fin 4 → ℝ := fun i => (r i).im
  have hre : (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z).mulVec xr = 0 := by
    funext i
    have h := congrArg Complex.reCLM (hr i)
    simpa [Matrix.mulVec, dotProduct, xr, Complex.mul_re] using h
  have him : (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock z).mulVec xi = 0 := by
    funext i
    have h := congrArg Complex.imCLM (hr i)
    simpa [Matrix.mulVec, dotProduct, xi, Complex.mul_im] using h
  obtain ⟨cr, hcr⟩ :=
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_mulVec_eq_zero_iff_smul_kernel
      z xr).1 hre
  obtain ⟨ci, hci⟩ :=
    (gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_mulVec_eq_zero_iff_smul_kernel
      z xi).1 him
  refine ⟨(cr : ℂ) + Complex.I * (ci : ℂ), ?_⟩
  funext i
  have hcri := congrFun hcr i
  have hcii := congrFun hci i
  apply Complex.ext
  · simpa [xr, Pi.smul_apply, smul_eq_mul] using hcri
  · simpa [xi, Pi.smul_apply, smul_eq_mul] using hcii

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_kernel (z : ℕ × ℕ)
    (x : GammaSewnCriticalPhysicalPluckerHilbert)
    (hx : gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z x = 0) :
    ∃ c : ℂ, gammaSewnCriticalPhysicalPluckerRestriction z x = fun i => c *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i := by
  apply gammaSewnCriticalAdjacentPrime_PluckerSpectralBlock_complexKernel
  intro i
  have hcoord := gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_apply_coordinate z i x
  rw [hx, inner_zero_right] at hcoord
  have hw : (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z : ℂ) ≠ 0 := by
    exact_mod_cast (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).ne'
  exact (mul_eq_zero.mp hcoord.symm).resolve_left hw

theorem gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_apply_eq_zero_of_global (x : GammaSewnCriticalPhysicalPluckerHilbert)
    (hx : gammaSewnCriticalPhysicalPluckerSpectralOperator x = 0)
    (z : ℕ × ℕ) :
    gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z x = 0 := by
  let Lc : (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert) →L[ℂ] ℂ :=
    (innerSL ℂ x).comp
      (ContinuousLinearMap.apply ℂ GammaSewnCriticalPhysicalPluckerHilbert x)
  let Lr : (GammaSewnCriticalPhysicalPluckerHilbert →L[ℂ]
      GammaSewnCriticalPhysicalPluckerHilbert) →L[ℝ] ℝ :=
    Complex.reCLM.comp (Lc.restrictScalars ℝ)
  let f : (ℕ × ℕ) → ℝ :=
    fun w => Lr (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator w)
  have hsumf : Summable f :=
    summable_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator.mapL Lr
  have hfnonneg (w : ℕ × ℕ) : 0 ≤ f w := by
    simpa [f, Lr, Lc, ContinuousLinearMap.reApplyInnerSelf_apply,
      inner_re_symm] using
        (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive w).re_inner_nonneg_right x
  have htsum0 : ∑' w, f w = 0 := by
    have hmap := Lr.map_tsum
      summable_gammaSewnCriticalPhysicalPluckerSpectralBlockOperator
    rw [← gammaSewnCriticalPhysicalPluckerSpectralOperator_eq_tsum_blocks] at hmap
    simpa [f, Lr, Lc, ContinuousLinearMap.reApplyInnerSelf_apply,
      inner_re_symm, hx] using hmap.symm
  have hf0 : f z = 0 := by
    apply le_antisymm
    · calc
        f z ≤ ∑' w, f w := hsumf.le_tsum z (fun w _ => hfnonneg w)
        _ = 0 := htsum0
    · exact hfnonneg z
  let q := inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z x)
  have hqre : q.re = 0 := by
    simpa [f, Lr, Lc, q, ContinuousLinearMap.reApplyInnerSelf_apply,
      inner_re_symm] using hf0
  have hqreal : (q.re : ℂ) = q := by
    have hs :=
      (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive z).inner_left_eq_inner_right x x
    have hc : star q = q := by
      calc
        star q = inner ℂ (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator z x) x :=
          inner_conj_symm _ _
        _ = q := hs
    exact (Complex.conj_eq_iff_re).mp hc
  apply (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_isPositive z).apply_eq_zero_of_inner_eq_zero
  change q = 0
  rw [← hqreal, hqre]
  simp

theorem gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_eq
    (x : GammaSewnCriticalPhysicalPluckerHilbert)
    (c : ℕ → ℂ)
    (hc : ∀ e, gammaSewnCriticalPhysicalPluckerRestriction (e, 0) x = fun i => c e *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, 0) i)
    (e : ℕ) : c (e + 1) = c e := by
  have he := congrFun (hc e) (1 : Fin 4)
  have hes := congrFun (hc (e + 1)) (0 : Fin 4)
  have hshared : gammaSewnCriticalPhysicalPluckerRestriction (e, 0) x 1 =
      gammaSewnCriticalPhysicalPluckerRestriction (e + 1, 0) x 0 := by
    rw [gammaSewnCriticalPhysicalPluckerRestriction_apply, gammaSewnCriticalPhysicalPluckerRestriction_apply]
    rfl
  have hmul : c e *
      (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, 0) 1 : ℂ) =
      c (e + 1) *
      (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, 0) 1 : ℂ) := by
    rw [← he, hshared, hes, gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_depth_overlap]
  have hk :
      (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, 0) 1 : ℂ) ≠ 0 := by
    exact_mod_cast
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero (e, 0) 1
  exact (mul_right_cancel₀ hk hmul).symm

theorem gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_zero
    (x : GammaSewnCriticalPhysicalPluckerHilbert)
    (c : ℕ → ℂ)
    (hc : ∀ e, gammaSewnCriticalPhysicalPluckerRestriction (e, 0) x = fun i => c e *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, 0) i) :
    c 0 = 0 := by
  have hcconst : ∀ e, c e = c 0 := by
    intro e
    induction e with
    | zero => rfl
    | succ e ih =>
        rw [gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_eq x c hc e, ih]
  by_contra hc0
  let W : ℝ := RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
    (gammaSewnCriticalAdjacentPrime_lower 0)
  have hW : 0 < W :=
    RHTower.gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) _
  let d : ℝ := (‖c 0‖ * W) ^ 2
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hxcoord (e : ℕ) : x (e, 0) =
      c 0 * (RHTower.gammaSewnMobiusApertureStokesGap (1 / 2)
        (gammaSewnCriticalAdjacentPrime_lower 0, e) : ℂ) := by
    have he := congrFun (hc e) (0 : Fin 4)
    rw [gammaSewnCriticalPhysicalPluckerRestriction_apply] at he
    simpa [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel,
      hcconst e, gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_zero_eq_stokesGap] using he
  have hlower (e : ℕ) : d ≤ ‖x (e, 0)‖ ^ 2 := by
    rw [hxcoord, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (RHTower.gammaSewnMobiusApertureStokesGap_pos (by norm_num) _)]
    unfold RHTower.gammaSewnMobiusApertureStokesGap
    dsimp [d, W]
    have hnat : (1 : ℝ) ≤ (e : ℝ) + 1 := by norm_num
    have hW0 : 0 ≤ RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
        (gammaSewnCriticalAdjacentPrime_lower 0) := by
      simpa [W] using hW.le
    have hfactor :
        RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
            (gammaSewnCriticalAdjacentPrime_lower 0) ≤
          ((e : ℝ) + 1) *
            RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
              (gammaSewnCriticalAdjacentPrime_lower 0) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hnat hW0
    have hleft : 0 ≤ ‖c 0‖ *
        RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower 0) :=
      mul_nonneg (norm_nonneg _) hW.le
    have hright : 0 ≤ ‖c 0‖ *
        (((e : ℝ) + 1) * RHTower.gammaSewnMobiusApertureStokesInverseTilt (1 / 2)
          (gammaSewnCriticalAdjacentPrime_lower 0)) := by positivity
    exact (sq_le_sq₀ hleft hright).2
      (mul_le_mul_of_nonneg_left
        hfactor (norm_nonneg _))
  have hsum : Summable (fun e : ℕ => ‖x (e, 0)‖ ^ 2) := by
    exact (HilbertSchmidt.summable_coe_sq x).comp_injective
      (fun _ _ h => congrArg Prod.fst h)
  have hconst : Summable (fun _ : ℕ => d) := by
    exact Summable.of_nonneg_of_le (fun _ => hd.le) hlower hsum
  haveI : Finite ℕ := Finite.of_summable_const hd hconst
  exact not_finite ℕ

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_injective :
    Function.Injective gammaSewnCriticalPhysicalPluckerSpectralOperator := by
  intro x y hxy
  have hkernel : gammaSewnCriticalPhysicalPluckerSpectralOperator (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hex (z : ℕ × ℕ) : ∃ c : ℂ, gammaSewnCriticalPhysicalPluckerRestriction z (x - y) = fun i => c *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector z i :=
    gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_kernel z (x - y) (gammaSewnCriticalPhysicalPluckerSpectralBlockOperator_apply_eq_zero_of_global (x - y) hkernel z)
  choose c hc using hex
  have hcdepth : ∀ e, gammaSewnCriticalPhysicalPluckerRestriction (e, 0) (x - y) = fun i => c (e, 0) *
      gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, 0) i := by
    intro e
    exact hc (e, 0)
  have hc00 : c (0, 0) = 0 :=
    gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_zero (x - y) (fun e => c (e, 0)) hcdepth
  have hcfirst : ∀ e, c (e, 0) = 0 := by
    intro e
    induction e with
    | zero => exact hc00
    | succ e ih =>
        rw [gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_eq (x - y) (fun k => c (k, 0)) hcdepth e, ih]
  have hrow (e : ℕ) : ∀ n, (x - y) (e, n) = 0 := by
    intro n
    induction n with
    | zero =>
        have h0 := congrFun (hc (e, 0)) (0 : Fin 4)
        rw [gammaSewnCriticalPhysicalPluckerRestriction_apply] at h0
        simpa [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel, hcfirst e] using h0
    | succ n ih =>
        have h0 := congrFun (hc (e, n)) (0 : Fin 4)
        rw [gammaSewnCriticalPhysicalPluckerRestriction_apply] at h0
        have hcoeff : c (e, n) = 0 := by
          have hk :
              (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, n) 0 : ℂ) ≠ 0 := by
            exact_mod_cast
              gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector_apply_ne_zero (e, n) 0
          have h0' : (x - y) (e, n) = c (e, n) *
              (gammaSewnCriticalAdjacentPrime_PluckerSpectralKernelVector (e, n) 0 : ℂ) := by
            simpa [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel] using h0
          rw [ih] at h0'
          exact (mul_eq_zero.mp h0'.symm).resolve_right hk
        have h2 := congrFun (hc (e, n)) (2 : Fin 4)
        rw [gammaSewnCriticalPhysicalPluckerRestriction_apply] at h2
        simpa [gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel, hcoeff] using h2
  apply sub_eq_zero.mp
  ext u
  rcases u with ⟨e, n⟩
  exact hrow e n

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_eq_zero_iff
    (x : GammaSewnCriticalPhysicalPluckerHilbert) :
    gammaSewnCriticalPhysicalPluckerSpectralOperator x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply gammaSewnCriticalPhysicalPluckerSpectralOperator_injective
    simpa using hx
  · rintro rfl
    exact map_zero _

theorem gammaSewnCriticalPhysicalPluckerSpectralOperator_re_inner_pos_iff
    (x : GammaSewnCriticalPhysicalPluckerHilbert) :
    0 < (inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x)).re ↔ x ≠ 0 := by
  constructor
  · intro hpos hx
    subst x
    simp at hpos
  · intro hx
    have hnonneg :=
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.re_inner_nonneg_right x
    apply lt_of_le_of_ne hnonneg
    intro hre
    have hqreal :
        (((inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x)).re : ℂ)) =
          inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x) := by
      have hs := gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.inner_left_eq_inner_right x x
      have hc : star (inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x)) =
          inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x) := by
        calc
          star (inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x)) =
              inner ℂ (gammaSewnCriticalPhysicalPluckerSpectralOperator x) x :=
            inner_conj_symm _ _
          _ = _ := hs
      exact (Complex.conj_eq_iff_re).mp hc
    have hinner : inner ℂ x (gammaSewnCriticalPhysicalPluckerSpectralOperator x) = 0 := by
      calc
        _ = (((inner ℂ x
            (gammaSewnCriticalPhysicalPluckerSpectralOperator x)).re : ℂ)) := hqreal.symm
        _ = 0 := by exact_mod_cast hre.symm
    have happly :=
      gammaSewnCriticalPhysicalPluckerSpectralOperator_isPositive.apply_eq_zero_of_inner_eq_zero
        hinner
    exact hx ((gammaSewnCriticalPhysicalPluckerSpectralOperator_apply_eq_zero_iff x).1 happly)

end RHTower.HedenmalmThetaSource

