import GaloisForLFunctions.HTGeometry.ClockSolutionPureSecondFst

/-!
# The algebra of admissible potentials

The effective potential of a scale function is a sum of products of the scale, its derivatives and
an exponential. To recognise such a combination as admissible it is enough to know that the class of
admissible potentials is closed under the operations used to build it.

This file records those closures. An admissible potential is one which is holomorphic and bounded on
a strip in the transverse variable, continuously differentiable in the two null coordinates, and —
for the probe to be real — real on the real transverse axis. Sums, differences, products and
constants stay in the class, with the bounds adding and multiplying as expected.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- A potential holomorphic and bounded on a strip, continuously differentiable in the two null
coordinates. -/
structure BoundedC1Potential (V Vs Vt : ℝ → ℝ → ℂ → ℂ) (ρ Mv : ℝ) : Prop where
  potC1 : StripPotentialC1 V Vs Vt ρ
  boundNonneg : 0 ≤ Mv
  bound : ∀ s t : ℝ, ∀ z ∈ imStrip ρ, ‖V s t z‖ ≤ Mv

/-- A potential taking real values on the real transverse axis. -/
def RealOnAxis (V : ℝ → ℝ → ℂ → ℂ) : Prop := ∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0

namespace BoundedC1Potential

variable {V Vs Vt W Ws Wt : ℝ → ℝ → ℂ → ℂ} {ρ M N : ℝ}

theorem add (hV : BoundedC1Potential V Vs Vt ρ M) (hW : BoundedC1Potential W Ws Wt ρ N) :
    BoundedC1Potential (fun s t z => V s t z + W s t z) (fun s t z => Vs s t z + Ws s t z)
      (fun s t z => Vt s t z + Wt s t z) ρ (M + N) where
  potC1 :=
    { base :=
        { cont := hV.potC1.base.cont.add hW.potC1.base.cont
          holo := fun s t => (hV.potC1.base.holo s t).add (hW.potC1.base.holo s t) }
      hasDerivFst := fun s t z hz =>
        (hV.potC1.hasDerivFst s t z hz).add (hW.potC1.hasDerivFst s t z hz)
      hasDerivSnd := fun s t z hz =>
        (hV.potC1.hasDerivSnd s t z hz).add (hW.potC1.hasDerivSnd s t z hz)
      contFst := hV.potC1.contFst.add hW.potC1.contFst
      contSnd := hV.potC1.contSnd.add hW.potC1.contSnd }
  boundNonneg := add_nonneg hV.boundNonneg hW.boundNonneg
  bound := fun s t z hz =>
    le_trans (norm_add_le _ _) (add_le_add (hV.bound s t z hz) (hW.bound s t z hz))

theorem sub (hV : BoundedC1Potential V Vs Vt ρ M) (hW : BoundedC1Potential W Ws Wt ρ N) :
    BoundedC1Potential (fun s t z => V s t z - W s t z) (fun s t z => Vs s t z - Ws s t z)
      (fun s t z => Vt s t z - Wt s t z) ρ (M + N) where
  potC1 :=
    { base :=
        { cont := hV.potC1.base.cont.sub hW.potC1.base.cont
          holo := fun s t => (hV.potC1.base.holo s t).sub (hW.potC1.base.holo s t) }
      hasDerivFst := fun s t z hz =>
        (hV.potC1.hasDerivFst s t z hz).sub (hW.potC1.hasDerivFst s t z hz)
      hasDerivSnd := fun s t z hz =>
        (hV.potC1.hasDerivSnd s t z hz).sub (hW.potC1.hasDerivSnd s t z hz)
      contFst := hV.potC1.contFst.sub hW.potC1.contFst
      contSnd := hV.potC1.contSnd.sub hW.potC1.contSnd }
  boundNonneg := add_nonneg hV.boundNonneg hW.boundNonneg
  bound := fun s t z hz =>
    le_trans (norm_sub_le _ _) (add_le_add (hV.bound s t z hz) (hW.bound s t z hz))

theorem mul (hV : BoundedC1Potential V Vs Vt ρ M) (hW : BoundedC1Potential W Ws Wt ρ N) :
    BoundedC1Potential (fun s t z => V s t z * W s t z)
      (fun s t z => Vs s t z * W s t z + V s t z * Ws s t z)
      (fun s t z => Vt s t z * W s t z + V s t z * Wt s t z) ρ (M * N) where
  potC1 :=
    { base :=
        { cont := hV.potC1.base.cont.mul hW.potC1.base.cont
          holo := fun s t => (hV.potC1.base.holo s t).mul (hW.potC1.base.holo s t) }
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
    BoundedC1Potential (fun _ _ _ => c) (fun _ _ _ => 0) (fun _ _ _ => 0) ρ ‖c‖ where
  potC1 :=
    { base :=
        { cont := continuousOn_const
          holo := fun _ _ => differentiableOn_const c }
      hasDerivFst := fun _ _ _ _ => hasDerivAt_const _ _
      hasDerivSnd := fun _ _ _ _ => hasDerivAt_const _ _
      contFst := continuousOn_const
      contSnd := continuousOn_const }
  boundNonneg := norm_nonneg c
  bound := fun _ _ _ _ => le_rfl

/-- Replacing the derivative functions by equal ones. -/
theorem congr_deriv (hV : BoundedC1Potential V Vs Vt ρ M) {Vs' Vt' : ℝ → ℝ → ℂ → ℂ}
    (hs : Vs' = Vs) (ht : Vt' = Vt) : BoundedC1Potential V Vs' Vt' ρ M := by
  subst hs
  subst ht
  exact hV

/-- Enlarging the bound keeps a potential admissible. -/
theorem mono (hV : BoundedC1Potential V Vs Vt ρ M) {N : ℝ} (h : M ≤ N) :
    BoundedC1Potential V Vs Vt ρ N where
  potC1 := hV.potC1
  boundNonneg := le_trans hV.boundNonneg h
  bound := fun s t z hz => le_trans (hV.bound s t z hz) h

/-! ## Atoms -/

/-- A function of the first null coordinate alone is admissible. -/
theorem ofFst {f f' : ℝ → ℝ} (hf : ∀ s, HasDerivAt f (f' s) s) (hcf : Continuous f)
    (hcf' : Continuous f') {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s, |f s| ≤ M) (ρ : ℝ) :
    BoundedC1Potential (fun s _ _ => ((f s : ℝ) : ℂ)) (fun s _ _ => ((f' s : ℝ) : ℂ))
      (fun _ _ _ => 0) ρ M where
  potC1 :=
    { base :=
        { cont := (Complex.continuous_ofReal.comp
            (hcf.comp (continuous_fst.comp continuous_fst))).continuousOn
          holo := fun _ _ => differentiableOn_const _ }
      hasDerivFst := fun s _ _ _ =>
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hf s)
      hasDerivSnd := fun _ _ _ _ => hasDerivAt_const _ _
      contFst := (Complex.continuous_ofReal.comp
        (hcf'.comp (continuous_fst.comp continuous_fst))).continuousOn
      contSnd := continuousOn_const }
  boundNonneg := hM0
  bound := fun s _ _ _ => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM s

/-- A function of the second null coordinate alone is admissible. -/
theorem ofSnd {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t) (hcf : Continuous f)
    (hcf' : Continuous f') {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ t, |f t| ≤ M) (ρ : ℝ) :
    BoundedC1Potential (fun _ t _ => ((f t : ℝ) : ℂ)) (fun _ _ _ => 0)
      (fun _ t _ => ((f' t : ℝ) : ℂ)) ρ M where
  potC1 :=
    { base :=
        { cont := (Complex.continuous_ofReal.comp
            (hcf.comp (continuous_snd.comp continuous_fst))).continuousOn
          holo := fun _ _ => differentiableOn_const _ }
      hasDerivFst := fun _ _ _ _ => hasDerivAt_const _ _
      hasDerivSnd := fun _ t _ _ =>
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hf t)
      contFst := continuousOn_const
      contSnd := (Complex.continuous_ofReal.comp
        (hcf'.comp (continuous_snd.comp continuous_fst))).continuousOn }
  boundNonneg := hM0
  bound := fun _ t _ _ => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM t

/-- A holomorphic function of the transverse variable alone is admissible on any strip where it is
bounded. -/
theorem ofTransverse {g : ℂ → ℂ} (hg : Differentiable ℂ g) {ρ M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ imStrip ρ, ‖g z‖ ≤ M) :
    BoundedC1Potential (fun _ _ z => g z) (fun _ _ _ => 0) (fun _ _ _ => 0) ρ M where
  potC1 :=
    { base :=
        { cont := (hg.continuous.comp continuous_snd).continuousOn
          holo := fun _ _ => hg.differentiableOn }
      hasDerivFst := fun _ _ _ _ => hasDerivAt_const _ _
      hasDerivSnd := fun _ _ _ _ => hasDerivAt_const _ _
      contFst := continuousOn_const
      contSnd := continuousOn_const }
  boundNonneg := hM0
  bound := fun _ _ z hz => hM z hz

/-- **A holomorphic function of the sum of the three coordinates is admissible** on any strip where
it is bounded. This is the atom with genuinely coupled dependence: it is a function of neither the
null coordinates alone nor the transverse one alone. -/
theorem ofSum {g g' : ℂ → ℂ} (hg : ∀ w : ℂ, HasDerivAt g (g' w) w) (hg'c : Continuous g')
    {ρ M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ s t : ℝ, ∀ z ∈ imStrip ρ, ‖g ((s : ℂ) + (t : ℂ) + z)‖ ≤ M) :
    BoundedC1Potential (fun s t z => g ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => g' ((s : ℂ) + (t : ℂ) + z))
      (fun s t z => g' ((s : ℂ) + (t : ℂ) + z)) ρ M where
  potC1 :=
    { base :=
        { cont := by
            have hgc : Continuous g := continuous_iff_continuousAt.mpr fun w => (hg w).continuousAt
            have hmap : Continuous fun q : (ℝ × ℝ) × ℂ =>
                ((q.1.1 : ℂ) + (q.1.2 : ℂ) + q.2) :=
              ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).add
                (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst))).add
                continuous_snd
            exact (hgc.comp hmap).continuousOn
          holo := fun s t => by
            have hgd : Differentiable ℂ g := fun w => (hg w).differentiableAt
            have hcomp : Differentiable ℂ fun z : ℂ => g ((s : ℂ) + (t : ℂ) + z) :=
              hgd.comp ((differentiable_const ((s : ℂ) + (t : ℂ))).add differentiable_id)
            exact hcomp.differentiableOn }
      hasDerivFst := fun s t z _ => by
        have hEq : (fun x : ℝ => g ((x : ℂ) + (t : ℂ) + z))
            = fun x : ℝ => g ((x : ℂ) + ((t : ℂ) + z)) := by
          funext x
          congr 1
          ring
        rw [hEq]
        have h2 := ((hg ((s : ℂ) + ((t : ℂ) + z))).comp_add_const (s : ℂ)
          ((t : ℂ) + z)).comp_ofReal
        have hval : g' ((s : ℂ) + ((t : ℂ) + z)) = g' ((s : ℂ) + (t : ℂ) + z) := by
          congr 1
          ring
        rwa [hval] at h2
      hasDerivSnd := fun s t z _ => by
        have hEq : (fun x : ℝ => g ((s : ℂ) + (x : ℂ) + z))
            = fun x : ℝ => g ((x : ℂ) + ((s : ℂ) + z)) := by
          funext x
          congr 1
          ring
        rw [hEq]
        have h2 := ((hg ((t : ℂ) + ((s : ℂ) + z))).comp_add_const (t : ℂ)
          ((s : ℂ) + z)).comp_ofReal
        have hval : g' ((t : ℂ) + ((s : ℂ) + z)) = g' ((s : ℂ) + (t : ℂ) + z) := by
          congr 1
          ring
        rwa [hval] at h2
      contFst := by
        have hmap : Continuous fun q : (ℝ × ℝ) × ℂ => ((q.1.1 : ℂ) + (q.1.2 : ℂ) + q.2) :=
          ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).add
            (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst))).add
            continuous_snd
        exact (hg'c.comp hmap).continuousOn
      contSnd := by
        have hmap : Continuous fun q : (ℝ × ℝ) × ℂ => ((q.1.1 : ℂ) + (q.1.2 : ℂ) + q.2) :=
          ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).add
            (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst))).add
            continuous_snd
        exact (hg'c.comp hmap).continuousOn }
  boundNonneg := hM0
  bound := hM

/-- **The exponential of twice an admissible potential is admissible.** -/
theorem cexp_two (hV : BoundedC1Potential V Vs Vt ρ M) :
    BoundedC1Potential (fun s t z => Complex.exp (2 * V s t z))
      (fun s t z => Complex.exp (2 * V s t z) * (2 * Vs s t z))
      (fun s t z => Complex.exp (2 * V s t z) * (2 * Vt s t z)) ρ (Real.exp (2 * M)) where
  potC1 :=
    { base :=
        { cont := by
            have h := hV.potC1.base.cont
            exact (Complex.continuous_exp.comp_continuousOn
              (continuousOn_const.mul h))
          holo := fun s t =>
            Complex.differentiable_exp.comp_differentiableOn
              ((differentiableOn_const 2).mul (hV.potC1.base.holo s t)) }
      hasDerivFst := fun s t z hz => ((hV.potC1.hasDerivFst s t z hz).const_mul 2).cexp
      hasDerivSnd := fun s t z hz => ((hV.potC1.hasDerivSnd s t z hz).const_mul 2).cexp
      contFst := by
        have h := hV.potC1.base.cont
        exact ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul h)).mul
          (continuousOn_const.mul hV.potC1.contFst))
      contSnd := by
        have h := hV.potC1.base.cont
        exact ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul h)).mul
          (continuousOn_const.mul hV.potC1.contSnd)) }
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

end BoundedC1Potential

namespace RealOnAxis

variable {V W : ℝ → ℝ → ℂ → ℂ}

theorem add (hV : RealOnAxis V) (hW : RealOnAxis W) :
    RealOnAxis fun s t z => V s t z + W s t z := by
  intro s t w
  rw [Complex.add_im, hV s t w, hW s t w, add_zero]

theorem sub (hV : RealOnAxis V) (hW : RealOnAxis W) :
    RealOnAxis fun s t z => V s t z - W s t z := by
  intro s t w
  rw [Complex.sub_im, hV s t w, hW s t w, sub_zero]

theorem mul (hV : RealOnAxis V) (hW : RealOnAxis W) :
    RealOnAxis fun s t z => V s t z * W s t z := by
  intro s t w
  rw [Complex.mul_im, hV s t w, hW s t w]
  ring

theorem const {c : ℂ} (hc : c.im = 0) :
    RealOnAxis (fun _ _ _ => c : ℝ → ℝ → ℂ → ℂ) := fun _ _ _ => hc

end RealOnAxis

end GaloisForLFunctions.HTGeometry
