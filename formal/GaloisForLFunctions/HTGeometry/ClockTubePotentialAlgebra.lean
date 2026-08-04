import GaloisForLFunctions.HTGeometry.ClockTubeRealKernels

/-!
# An algebra of admissible potentials on a tube

The clock construction on a tube asks a potential to be slice holomorphic, bounded, and continuously
differentiable in the two null coordinates. Those three conditions are stable under sums, differences
and products, and they hold for the atoms the examples are built from. This file records that
algebra, so that a concrete potential can be certified by composing closure lemmas rather than by
re-proving the conditions.

The atom with genuinely coupled dependence is a holomorphic function of `ξ + η + z¹ + ⋯ + zᵏ`: it is
a function of neither the null coordinates alone nor the transverse ones alone, and not a sum or a
product of one-variable profiles.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The sum of the transverse coordinates, as a continuous linear map. -/
noncomputable def sumCLM (k : ℕ) : (Fin k → ℂ) →L[ℂ] ℂ :=
  ∑ i, ContinuousLinearMap.proj i

theorem sumCLM_apply (w : Fin k → ℂ) : sumCLM k w = ∑ i, w i := by
  simp [sumCLM]

theorem continuous_transverseSum : Continuous fun z : Fin k → ℂ => ∑ i, z i :=
  continuous_finsetSum Finset.univ fun i _ => continuous_apply i

/-- The sum of the transverse coordinates, along a coordinate slice, is differentiable. -/
theorem differentiable_transverseSumSlice (z : Fin k → ℂ) (i : Fin k) :
    Differentiable ℂ fun ζ : ℂ => ∑ j, Function.update z i ζ j := by
  have heq : (fun ζ : ℂ => sumCLM k (Function.update z i ζ))
      = fun ζ : ℂ => ∑ j, Function.update z i ζ j := by
    funext ζ
    rw [sumCLM_apply]
  rw [← heq]
  exact (sumCLM k).differentiable.comp (differentiable_updateSlice z i)

/-- An admissible potential of the clock construction on a tube. -/
structure BoundedC1TubePotential (V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ρ Mv : ℝ) : Prop where
  potC1 : TubePotentialC1 V Vs Vt ρ
  boundNonneg : 0 ≤ Mv
  bound : ∀ s t : ℝ, ∀ z ∈ tube k ρ, ‖V s t z‖ ≤ Mv

/-- A potential real at real transverse points. -/
def RealOnAxisTube (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) : Prop :=
  ∀ (s t : ℝ) (y : Fin k → ℝ), (V s t (realTube y)).im = 0

namespace BoundedC1TubePotential

variable {V Vs Vt W Ws Wt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ M N : ℝ}

theorem add (hV : BoundedC1TubePotential V Vs Vt ρ M)
    (hW : BoundedC1TubePotential W Ws Wt ρ N) :
    BoundedC1TubePotential (fun s t z => V s t z + W s t z) (fun s t z => Vs s t z + Ws s t z)
      (fun s t z => Vt s t z + Wt s t z) ρ (M + N) where
  potC1 :=
    { base :=
        { cont := hV.potC1.base.cont.add hW.potC1.base.cont
          holo := fun s t z hz i =>
            ((hV.potC1.base.holo s t) z hz i).add ((hW.potC1.base.holo s t) z hz i) }
      hasDerivFst := fun s t z hz =>
        (hV.potC1.hasDerivFst s t z hz).add (hW.potC1.hasDerivFst s t z hz)
      hasDerivSnd := fun s t z hz =>
        (hV.potC1.hasDerivSnd s t z hz).add (hW.potC1.hasDerivSnd s t z hz)
      contFst := hV.potC1.contFst.add hW.potC1.contFst
      contSnd := hV.potC1.contSnd.add hW.potC1.contSnd }
  boundNonneg := add_nonneg hV.boundNonneg hW.boundNonneg
  bound := fun s t z hz =>
    le_trans (norm_add_le _ _) (add_le_add (hV.bound s t z hz) (hW.bound s t z hz))

theorem sub (hV : BoundedC1TubePotential V Vs Vt ρ M)
    (hW : BoundedC1TubePotential W Ws Wt ρ N) :
    BoundedC1TubePotential (fun s t z => V s t z - W s t z) (fun s t z => Vs s t z - Ws s t z)
      (fun s t z => Vt s t z - Wt s t z) ρ (M + N) where
  potC1 :=
    { base :=
        { cont := hV.potC1.base.cont.sub hW.potC1.base.cont
          holo := fun s t z hz i =>
            ((hV.potC1.base.holo s t) z hz i).sub ((hW.potC1.base.holo s t) z hz i) }
      hasDerivFst := fun s t z hz =>
        (hV.potC1.hasDerivFst s t z hz).sub (hW.potC1.hasDerivFst s t z hz)
      hasDerivSnd := fun s t z hz =>
        (hV.potC1.hasDerivSnd s t z hz).sub (hW.potC1.hasDerivSnd s t z hz)
      contFst := hV.potC1.contFst.sub hW.potC1.contFst
      contSnd := hV.potC1.contSnd.sub hW.potC1.contSnd }
  boundNonneg := add_nonneg hV.boundNonneg hW.boundNonneg
  bound := fun s t z hz =>
    le_trans (norm_sub_le _ _) (add_le_add (hV.bound s t z hz) (hW.bound s t z hz))

theorem mul (hV : BoundedC1TubePotential V Vs Vt ρ M)
    (hW : BoundedC1TubePotential W Ws Wt ρ N) :
    BoundedC1TubePotential (fun s t z => V s t z * W s t z)
      (fun s t z => Vs s t z * W s t z + V s t z * Ws s t z)
      (fun s t z => Vt s t z * W s t z + V s t z * Wt s t z) ρ (M * N) where
  potC1 :=
    { base :=
        { cont := hV.potC1.base.cont.mul hW.potC1.base.cont
          holo := fun s t z hz i =>
            ((hV.potC1.base.holo s t) z hz i).mul ((hW.potC1.base.holo s t) z hz i) }
      hasDerivFst := fun s t z hz =>
        (hV.potC1.hasDerivFst s t z hz).mul (hW.potC1.hasDerivFst s t z hz)
      hasDerivSnd := fun s t z hz =>
        (hV.potC1.hasDerivSnd s t z hz).mul (hW.potC1.hasDerivSnd s t z hz)
      contFst := (hV.potC1.contFst.mul hW.potC1.base.cont).add
        (hV.potC1.base.cont.mul hW.potC1.contFst)
      contSnd := (hV.potC1.contSnd.mul hW.potC1.base.cont).add
        (hV.potC1.base.cont.mul hW.potC1.contSnd) }
  boundNonneg := mul_nonneg hV.boundNonneg hW.boundNonneg
  bound := fun s t z hz => by
    rw [norm_mul]
    exact mul_le_mul (hV.bound s t z hz) (hW.bound s t z hz) (norm_nonneg _) hV.boundNonneg

/-- A constant potential is admissible. -/
theorem const (c : ℂ) (ρ : ℝ) :
    BoundedC1TubePotential (k := k) (fun _ _ _ => c) (fun _ _ _ => 0) (fun _ _ _ => 0)
      ρ ‖c‖ where
  potC1 :=
    { base :=
        { cont := continuousOn_const
          holo := fun _ _ _ _ _ => differentiableOn_const c }
      hasDerivFst := fun _ _ _ _ => hasDerivAt_const _ _
      hasDerivSnd := fun _ _ _ _ => hasDerivAt_const _ _
      contFst := continuousOn_const
      contSnd := continuousOn_const }
  boundNonneg := norm_nonneg c
  bound := fun _ _ _ _ => le_rfl

/-- Replacing the derivative functions by equal ones. -/
theorem congr_deriv (hV : BoundedC1TubePotential V Vs Vt ρ M)
    {Vs' Vt' : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hs : Vs' = Vs) (ht : Vt' = Vt) :
    BoundedC1TubePotential V Vs' Vt' ρ M := by
  subst hs
  subst ht
  exact hV

/-- Enlarging the bound keeps a potential admissible. -/
theorem mono (hV : BoundedC1TubePotential V Vs Vt ρ M) {N : ℝ} (h : M ≤ N) :
    BoundedC1TubePotential V Vs Vt ρ N where
  potC1 := hV.potC1
  boundNonneg := le_trans hV.boundNonneg h
  bound := fun s t z hz => le_trans (hV.bound s t z hz) h

/-! ## The coupled atom -/

/-- **A holomorphic function of the sum of all the coordinates is admissible** on any tube where it
is bounded. This is the atom with genuinely coupled dependence. -/
theorem ofSum {g g' : ℂ → ℂ} (hg : ∀ w : ℂ, HasDerivAt g (g' w) w) (hg'c : Continuous g')
    {ρ M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s t : ℝ, ∀ z ∈ tube k ρ, ‖g ((s : ℂ) + (t : ℂ) + ∑ i, z i)‖ ≤ M) :
    BoundedC1TubePotential (k := k) (fun s t z => g ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => g' ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => g' ((s : ℂ) + (t : ℂ) + ∑ i, z i)) ρ M where
  potC1 :=
    { base :=
        { cont := by
            have hgc : Continuous g := continuous_iff_continuousAt.mpr fun w => (hg w).continuousAt
            have hmap : Continuous fun q : (ℝ × ℝ) × (Fin k → ℂ) =>
                ((q.1.1 : ℂ) + (q.1.2 : ℂ) + ∑ i, q.2 i) :=
              ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).add
                (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst))).add
                (continuous_transverseSum.comp continuous_snd)
            exact (hgc.comp hmap).continuousOn
          holo := fun s t z _ i => by
            have hgd : Differentiable ℂ g := fun w => (hg w).differentiableAt
            have hcomp : Differentiable ℂ fun ζ : ℂ =>
                g ((s : ℂ) + (t : ℂ) + ∑ j, Function.update z i ζ j) :=
              hgd.comp ((differentiable_const ((s : ℂ) + (t : ℂ))).add
                (differentiable_transverseSumSlice z i))
            exact hcomp.differentiableOn }
      hasDerivFst := fun s t z _ => by
        have hEq : (fun x : ℝ => g ((x : ℂ) + (t : ℂ) + ∑ i, z i))
            = fun x : ℝ => g ((x : ℂ) + ((t : ℂ) + ∑ i, z i)) := by
          funext x
          congr 1
          ring
        rw [hEq]
        have h2 := ((hg ((s : ℂ) + ((t : ℂ) + ∑ i, z i))).comp_add_const (s : ℂ)
          ((t : ℂ) + ∑ i, z i)).comp_ofReal
        have hval : g' ((s : ℂ) + ((t : ℂ) + ∑ i, z i)) = g' ((s : ℂ) + (t : ℂ) + ∑ i, z i) := by
          congr 1
          ring
        rwa [hval] at h2
      hasDerivSnd := fun s t z _ => by
        have hEq : (fun x : ℝ => g ((s : ℂ) + (x : ℂ) + ∑ i, z i))
            = fun x : ℝ => g ((x : ℂ) + ((s : ℂ) + ∑ i, z i)) := by
          funext x
          congr 1
          ring
        rw [hEq]
        have h2 := ((hg ((t : ℂ) + ((s : ℂ) + ∑ i, z i))).comp_add_const (t : ℂ)
          ((s : ℂ) + ∑ i, z i)).comp_ofReal
        have hval : g' ((t : ℂ) + ((s : ℂ) + ∑ i, z i)) = g' ((s : ℂ) + (t : ℂ) + ∑ i, z i) := by
          congr 1
          ring
        rwa [hval] at h2
      contFst := by
        have hmap : Continuous fun q : (ℝ × ℝ) × (Fin k → ℂ) =>
            ((q.1.1 : ℂ) + (q.1.2 : ℂ) + ∑ i, q.2 i) :=
          ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).add
            (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst))).add
            (continuous_transverseSum.comp continuous_snd)
        exact (hg'c.comp hmap).continuousOn
      contSnd := by
        have hmap : Continuous fun q : (ℝ × ℝ) × (Fin k → ℂ) =>
            ((q.1.1 : ℂ) + (q.1.2 : ℂ) + ∑ i, q.2 i) :=
          ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).add
            (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst))).add
            (continuous_transverseSum.comp continuous_snd)
        exact (hg'c.comp hmap).continuousOn }
  boundNonneg := hM0
  bound := hM

/-- **The exponential of twice an admissible potential is admissible.** -/
theorem cexp_two (hV : BoundedC1TubePotential V Vs Vt ρ M) :
    BoundedC1TubePotential (fun s t z => Complex.exp (2 * V s t z))
      (fun s t z => Complex.exp (2 * V s t z) * (2 * Vs s t z))
      (fun s t z => Complex.exp (2 * V s t z) * (2 * Vt s t z)) ρ (Real.exp (2 * M)) where
  potC1 :=
    { base :=
        { cont := Complex.continuous_exp.comp_continuousOn
            (continuousOn_const.mul hV.potC1.base.cont)
          holo := fun s t z hz i =>
            Complex.differentiable_exp.comp_differentiableOn
              ((differentiableOn_const 2).mul ((hV.potC1.base.holo s t) z hz i)) }
      hasDerivFst := fun s t z hz => ((hV.potC1.hasDerivFst s t z hz).const_mul 2).cexp
      hasDerivSnd := fun s t z hz => ((hV.potC1.hasDerivSnd s t z hz).const_mul 2).cexp
      contFst := (Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul hV.potC1.base.cont)).mul
        (continuousOn_const.mul hV.potC1.contFst)
      contSnd := (Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul hV.potC1.base.cont)).mul
        (continuousOn_const.mul hV.potC1.contSnd) }
  boundNonneg := (Real.exp_pos _).le
  bound := fun s t z hz => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (2 * V s t z).re ≤ ‖2 * V s t z‖ := Complex.re_le_norm _
    have h2 : ‖2 * V s t z‖ = 2 * ‖V s t z‖ := by
      rw [norm_mul]
      norm_num
    have h3 : ‖V s t z‖ ≤ M := hV.bound s t z hz
    linarith [h1, h2 ▸ h1]

end BoundedC1TubePotential

namespace RealOnAxisTube

variable {V W : ℝ → ℝ → (Fin k → ℂ) → ℂ}

theorem add (hV : RealOnAxisTube V) (hW : RealOnAxisTube W) :
    RealOnAxisTube fun s t z => V s t z + W s t z := by
  intro s t y
  rw [Complex.add_im, hV s t y, hW s t y, add_zero]

theorem sub (hV : RealOnAxisTube V) (hW : RealOnAxisTube W) :
    RealOnAxisTube fun s t z => V s t z - W s t z := by
  intro s t y
  rw [Complex.sub_im, hV s t y, hW s t y, sub_zero]

theorem mul (hV : RealOnAxisTube V) (hW : RealOnAxisTube W) :
    RealOnAxisTube fun s t z => V s t z * W s t z := by
  intro s t y
  rw [Complex.mul_im, hV s t y, hW s t y]
  ring

theorem const {c : ℂ} (hc : c.im = 0) :
    RealOnAxisTube (fun _ _ _ => c : ℝ → ℝ → (Fin k → ℂ) → ℂ) := fun _ _ _ => hc

end RealOnAxisTube

end GaloisForLFunctions.HTGeometry
