/-
# Polynomial `dlog` periods as root winding sums

The argument principle for polynomials in pure winding form: along any `C¹` loop avoiding the
roots, `∮ dlog P = Σ_root windInt(γ, root)` (with multiplicity) — by splitting `P` into linear
factors over `ℂ` and additivity of `logDeriv`.  No residues, no Rouché, no Jordan curve theorem.
This is the monodromy-counting instrument for the pair-case `GBExt` tower: the `φ₂`-monodromy of
a deep loop is `∮ dlog (f₂ⁿ)`, i.e. the winding sum over `quadraticPolyIterate`'s roots, each
term killable by the co-branch connector certificates.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.WindingCertificates
import GaloisForLFunctions.Bottcher.BasinBranching
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Complex Set Filter Metric Polynomial

namespace Bottcher

/-- The linear-factors product function of a root multiset. -/
noncomputable def rootsProd (s : Multiset ℂ) : ℂ → ℂ := fun z => (s.map (fun r => z - r)).prod

theorem rootsProd_zero : rootsProd 0 = fun _ => 1 := by
  funext z
  simp [rootsProd]

theorem rootsProd_cons (a : ℂ) (s : Multiset ℂ) :
    rootsProd (a ::ₘ s) = fun z => (z - a) * rootsProd s z := by
  funext z
  simp [rootsProd]

theorem differentiable_rootsProd (s : Multiset ℂ) : Differentiable ℂ (rootsProd s) := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [rootsProd_zero]
      exact differentiable_const 1
  | cons a s ih =>
      rw [rootsProd_cons]
      exact (differentiable_id.sub_const a).mul ih

theorem rootsProd_ne_zero {s : Multiset ℂ} {z : ℂ} (h : ∀ r ∈ s, z ≠ r) :
    rootsProd s z ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [rootsProd_zero]
      exact one_ne_zero
  | cons a s ih =>
      rw [rootsProd_cons]
      apply mul_ne_zero
      · exact sub_ne_zero.mpr (h a (Multiset.mem_cons_self a s))
      · exact ih (fun r hr => h r (Multiset.mem_cons_of_mem hr))

theorem analyticAt_rootsProd (s : Multiset ℂ) (z : ℂ) : AnalyticAt ℂ (rootsProd s) z := by
  induction s using Multiset.induction_on with
  | empty =>
      rw [rootsProd_zero]
      exact analyticAt_const
  | cons b t iht =>
      rw [rootsProd_cons]
      exact ((analyticAt_id.sub analyticAt_const).mul iht)

/-- **The winding sum over a root multiset.** -/
theorem windInt_logDeriv_rootsProd (s : Multiset ℂ) (ℓ : C1Loop)
    (h : ∀ θ : ℝ, ∀ r ∈ s, ℓ.γ θ ≠ r) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (rootsProd s) (ℓ.γ θ) * ℓ.γ' θ)
      = (s.map (fun r => windInt ℓ r)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      have h1 : ∀ θ : ℝ, logDeriv (rootsProd 0) (ℓ.γ θ) * ℓ.γ' θ = 0 := by
        intro θ
        rw [rootsProd_zero]
        rw [show logDeriv (fun _ : ℂ => (1:ℂ)) (ℓ.γ θ) = 0 from by
          rw [logDeriv_apply]
          simp]
        ring
      rw [intervalIntegral.integral_congr (fun θ _ => h1 θ)]
      simp
  | cons a s ih =>
      have havoid_a : ∀ θ, ℓ.γ θ ≠ a := fun θ => h θ a (Multiset.mem_cons_self a s)
      have havoid_s : ∀ θ : ℝ, ∀ r ∈ s, ℓ.γ θ ≠ r := fun θ r hr =>
        h θ r (Multiset.mem_cons_of_mem hr)
      have hsplit : ∀ θ : ℝ,
          logDeriv (rootsProd (a ::ₘ s)) (ℓ.γ θ) * ℓ.γ' θ
          = (ℓ.γ θ - a)⁻¹ * ℓ.γ' θ + logDeriv (rootsProd s) (ℓ.γ θ) * ℓ.γ' θ := by
        intro θ
        rw [rootsProd_cons]
        have h1 : logDeriv (fun z => (z - a) * rootsProd s z) (ℓ.γ θ)
            = logDeriv (fun z => z - a) (ℓ.γ θ) + logDeriv (rootsProd s) (ℓ.γ θ) :=
          logDeriv_mul (ℓ.γ θ) (sub_ne_zero.mpr (havoid_a θ))
            (rootsProd_ne_zero (havoid_s θ))
            (differentiable_id.sub_const a).differentiableAt
            (differentiable_rootsProd s).differentiableAt
        have h2 : logDeriv (fun z : ℂ => z - a) (ℓ.γ θ) = (ℓ.γ θ - a)⁻¹ := by
          rw [logDeriv_apply, deriv_sub_const, deriv_id'']
          rw [one_div]
        rw [h1, h2]
        ring
      rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ)]
      rw [intervalIntegral.integral_add]
      · rw [ih havoid_s]
        rw [show (∫ θ in (0:ℝ)..(2 * Real.pi), (ℓ.γ θ - a)⁻¹ * ℓ.γ' θ) = windInt ℓ a from rfl]
        simp
      · -- integrability of the winding integrand
        apply Continuous.intervalIntegrable
        have h1 : Continuous (fun θ => ℓ.γ θ - a) := ℓ.cont.sub continuous_const
        exact (h1.inv₀ (fun θ => sub_ne_zero.mpr (havoid_a θ))).mul ℓ.cont'
      · -- integrability of the tail integrand
        apply Continuous.intervalIntegrable
        have han : ∀ z : ℂ, AnalyticAt ℂ (rootsProd s) z := analyticAt_rootsProd s
        have h1 : Continuous (fun θ => deriv (rootsProd s) (ℓ.γ θ)) := by
          have h2 : Continuous (deriv (rootsProd s)) := by
            have h3 : AnalyticOnNhd ℂ (rootsProd s) Set.univ := fun z _ => han z
            exact (h3.deriv).continuousOn.comp_continuous continuous_id (fun z => trivial)
          exact h2.comp ℓ.cont
        have h2 : Continuous (fun θ => rootsProd s (ℓ.γ θ)) :=
          (differentiable_rootsProd s).continuous.comp ℓ.cont
        have h3 : Continuous (fun θ => logDeriv (rootsProd s) (ℓ.γ θ)) := by
          have h4 : (fun θ => logDeriv (rootsProd s) (ℓ.γ θ))
              = fun θ => deriv (rootsProd s) (ℓ.γ θ) / rootsProd s (ℓ.γ θ) := by
            funext θ
            rw [logDeriv_apply]
          rw [h4]
          exact h1.div h2 (fun θ => rootsProd_ne_zero (havoid_s θ))
        exact h3.mul ℓ.cont'

/-- **The argument principle, winding form**: for a nonzero polynomial and a loop avoiding its
roots, the `dlog` period is the winding sum over the roots with multiplicity. -/
theorem windInt_logDeriv_polynomial (P : Polynomial ℂ) (hP : P ≠ 0) (ℓ : C1Loop)
    (h : ∀ θ : ℝ, ∀ r ∈ P.roots, ℓ.γ θ ≠ r) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (fun z => P.eval z) (ℓ.γ θ) * ℓ.γ' θ)
      = (P.roots.map (fun r => windInt ℓ r)).sum := by
  have hsplits : P.Splits := IsAlgClosed.splits P
  have hfact : P = C P.leadingCoeff * (P.roots.map (fun a => X - C a)).prod :=
    Splits.eq_prod_roots hsplits
  have heval : ∀ z : ℂ, P.eval z = P.leadingCoeff * rootsProd P.roots z := by
    intro z
    conv_lhs => rw [hfact]
    rw [eval_mul, eval_C, rootsProd]
    congr 1
    rw [eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod ?_
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hL : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hcongr : ∀ θ : ℝ,
      logDeriv (fun z => P.eval z) (ℓ.γ θ) * ℓ.γ' θ
      = logDeriv (rootsProd P.roots) (ℓ.γ θ) * ℓ.γ' θ := by
    intro θ
    congr 1
    have h1 : (fun z => P.eval z) = fun z => P.leadingCoeff * rootsProd P.roots z := by
      funext z
      exact heval z
    rw [h1]
    have h2 : logDeriv (fun z => P.leadingCoeff * rootsProd P.roots z) (ℓ.γ θ)
        = logDeriv (fun _ => P.leadingCoeff) (ℓ.γ θ)
          + logDeriv (rootsProd P.roots) (ℓ.γ θ) :=
      logDeriv_mul (ℓ.γ θ) hL (rootsProd_ne_zero (h θ))
        (differentiableAt_const _) (differentiable_rootsProd _).differentiableAt
    rw [h2]
    rw [show logDeriv (fun _ : ℂ => P.leadingCoeff) (ℓ.γ θ) = 0 from by
      rw [logDeriv_apply]
      simp]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ)]
  exact windInt_logDeriv_rootsProd P.roots ℓ h

end Bottcher

namespace Bottcher

/-- The image of a `C¹` loop under a map analytic at its points. -/
noncomputable def C1Loop.map (ℓ : C1Loop) (f : ℂ → ℂ)
    (hf : ∀ θ : ℝ, AnalyticAt ℂ f (ℓ.γ θ)) : C1Loop where
  γ := fun θ => f (ℓ.γ θ)
  γ' := fun θ => _root_.deriv f (ℓ.γ θ) * ℓ.γ' θ
  cont := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact ((hf θ).continuousAt).comp ℓ.cont.continuousAt
  cont' := by
    apply Continuous.mul _ ℓ.cont'
    rw [continuous_iff_continuousAt]
    intro θ
    exact ((hf θ).deriv.continuousAt).comp ℓ.cont.continuousAt
  deriv := by
    intro θ hθ
    have h1 : HasDerivAt f (_root_.deriv f (ℓ.γ θ)) (ℓ.γ θ) :=
      (hf θ).differentiableAt.hasDerivAt
    exact h1.comp θ (ℓ.deriv θ hθ)
  closed := by
    show f (ℓ.γ (2 * Real.pi)) = f (ℓ.γ 0)
    rw [ℓ.closed]

theorem C1Loop.map_γ (ℓ : C1Loop) (f : ℂ → ℂ) (hf : ∀ θ : ℝ, AnalyticAt ℂ f (ℓ.γ θ)) :
    (ℓ.map f hf).γ = fun θ => f (ℓ.γ θ) := rfl

theorem C1Loop.map_γ' (ℓ : C1Loop) (f : ℂ → ℂ) (hf : ∀ θ : ℝ, AnalyticAt ℂ f (ℓ.γ θ)) :
    (ℓ.map f hf).γ' = fun θ => _root_.deriv f (ℓ.γ θ) * ℓ.γ' θ := rfl

/-- **`dlog` transport along a map**: the period of `g ∘ f` over a loop is the period of `g`
over the image loop. -/
theorem windInt_logDeriv_map (ℓ : C1Loop) (f g : ℂ → ℂ)
    (hf : ∀ θ : ℝ, AnalyticAt ℂ f (ℓ.γ θ))
    (hg : ∀ θ : ℝ, DifferentiableAt ℂ g (f (ℓ.γ θ))) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (fun z => g (f z)) (ℓ.γ θ) * ℓ.γ' θ)
      = ∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv g ((ℓ.map f hf).γ θ) * (ℓ.map f hf).γ' θ := by
  simp only [C1Loop.map_γ, C1Loop.map_γ']
  apply intervalIntegral.integral_congr
  intro θ _
  have h1 : logDeriv (g ∘ f) (ℓ.γ θ) = logDeriv g (f (ℓ.γ θ)) * deriv f (ℓ.γ θ) :=
    logDeriv_comp (hg θ) (hf θ).differentiableAt
  show logDeriv (fun z => g (f z)) (ℓ.γ θ) * ℓ.γ' θ
    = logDeriv g (f (ℓ.γ θ)) * (deriv f (ℓ.γ θ) * ℓ.γ' θ)
  rw [show (fun z => g (f z)) = g ∘ f from rfl, h1]
  ring

end Bottcher

namespace Bottcher

/-- **The iterate monodromy sum**: the `dlog` period of `f_c^[n]` along a loop avoiding the
level-`n` preimages of `0` is the winding sum over those preimages (the roots of
`quadraticPolyIterate`). -/
theorem windInt_logDeriv_quadratic_iterate (c : ℂ) (n : ℕ) (ℓ : C1Loop)
    (h : ∀ θ : ℝ, ∀ r ∈ (quadraticPolyIterate c n).roots, ℓ.γ θ ≠ r) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ) * ℓ.γ' θ)
      = ((quadraticPolyIterate c n).roots.map (fun r => windInt ℓ r)).sum := by
  have hne : quadraticPolyIterate c n ≠ 0 := by
    intro h0
    have h1 := quadraticPolyIterate_natDegree c n
    rw [h0] at h1
    simp at h1
    have h2 : (0:ℕ) < 2 ^ n := Nat.two_pow_pos n
    omega
  have hcongr : (fun z => (quadratic c)^[n] z)
      = fun z => (quadraticPolyIterate c n).eval z := by
    funext z
    rw [quadraticPolyIterate_eval]
  rw [hcongr]
  exact windInt_logDeriv_polynomial (quadraticPolyIterate c n) hne ℓ h

end Bottcher

namespace Bottcher

/-- If the loop winds around no level-`n` preimage of `0`, the `n`-th iterate's `dlog` period
vanishes — the `2ⁿ`-th-root existence condition for `φ ∘ f^[n]` along this loop. -/
theorem windInt_logDeriv_quadratic_iterate_eq_zero (c : ℂ) (n : ℕ) (ℓ : C1Loop)
    (havoid : ∀ θ : ℝ, ∀ r ∈ (quadraticPolyIterate c n).roots, ℓ.γ θ ≠ r)
    (hzero : ∀ r ∈ (quadraticPolyIterate c n).roots, windInt ℓ r = 0) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun z => (quadratic c)^[n] z) (ℓ.γ θ) * ℓ.γ' θ) = 0 := by
  rw [windInt_logDeriv_quadratic_iterate c n ℓ havoid]
  apply Multiset.sum_eq_zero
  intro x hx
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hx
  exact hzero r hr

end Bottcher
