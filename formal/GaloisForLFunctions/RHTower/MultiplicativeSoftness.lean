/-
# Multiplicative softness: the parity toggle and the location of the rigidity cut

Multiplying a member by the `V₄`-orbit quartic of an off-line, off-real point raises its vanishing
order there by exactly one, hence NEGATES its base-level deck charge (`(−1)^{ord}`).  A constraint
class that is stable under one such multiplication therefore always contains a member of nontrivial
charge — regardless of the member one starts from: either the seed already has odd order, or its
quartic multiple does.  Consequences:

* `isSoft_of_orbitQuartic_stable` — every quartic-multiplication-stable class with an analytic
  finite-order member near each off-line off-real point is soft (`PlantsArbitrary`): the softness
  of the FE + Schwarz class is an instance of a closure property, not a feature of one witness.
* `not_forcesRHParity_of_orbitQuartic_stable` — no such class forces RH-grade parity.
* `not_forcesRHParity_of_xi_orbitQuartic_stable` — the cut: a constraint class containing ξ that
  is stable under a SINGLE quartic multiplication (at one point beyond the wall) cannot force
  RH-grade parity.  A parity-deciding constraint must break stability under multiplication by
  FE-symmetric polynomials — it must couple to the coefficient/arithmetic structure, as the
  Dirichlet-series surgery rigidity does.
* `carriesChargeAt_mono`, `forcesRHParity_anti` — the constraint lattice is monotone: realized
  charge grows with the class, parity-forcing descends to subclasses.  Together with the toggle
  this squeezes the softness/rigidity boundary strictly above every multiplication-stable class.
-/
import GaloisForLFunctions.RHTower.GoldilocksTrichotomy
import GaloisForLFunctions.RHTower.RHLadderTheory

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The parity toggle -/

/-- Multiplying by the orbit quartic raises the vanishing order at its simple zero by one. -/
theorem analyticOrderAt_orbitQuartic_mul {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f ρ₀) :
    analyticOrderAt (fun s => orbitQuartic ρ₀ s * f s) ρ₀ = 1 + analyticOrderAt f ρ₀ := by
  have h := analyticOrderAt_mul ((orbitQuartic_differentiable ρ₀).analyticAt) hf
  rw [show (orbitQuartic ρ₀ * f) = (fun s => orbitQuartic ρ₀ s * f s) from rfl] at h
  rw [h, orbitQuartic_order_one hre him]

/-- **The parity toggle.**  Multiplying by the orbit quartic negates the base-level deck charge at
the quartic's zero: `(−1)^{1+ord} = −(−1)^{ord}`. -/
theorem carrierCharge_one_orbitQuartic_mul {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f ρ₀) (hford : analyticOrderAt f ρ₀ ≠ ⊤) :
    carrierCharge (fun s => orbitQuartic ρ₀ s * f s) 1 ρ₀ = - carrierCharge f 1 ρ₀ := by
  rw [carrierCharge_one_eq_neg_one_pow, carrierCharge_one_eq_neg_one_pow,
    analyticOrderAt_orbitQuartic_mul hre him hf, ENat.toNat_add (by simp) hford]
  simp [pow_add]

/-! ### §2 The softness metatheorem -/

/-- **Stability under one quartic multiplication produces nontrivial charge.**  If a class
contains an analytic finite-order member together with its orbit-quartic multiple, one of the two
has odd order at the point, so the class carries charge there.  No nonvanishing seed is needed:
the toggle covers both parities at once. -/
theorem carriesChargeAt_of_orbitQuartic_stable {C : (ℂ → ℂ) → Prop} {ρ₀ : ℂ}
    (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) {f : ℂ → ℂ} (hfC : C f)
    (hstab : C (fun s => orbitQuartic ρ₀ s * f s))
    (hfa : AnalyticAt ℂ f ρ₀) (hford : analyticOrderAt f ρ₀ ≠ ⊤) :
    CarriesChargeAt C ρ₀ := by
  by_cases hch : carrierCharge f 1 ρ₀ = 1
  · refine ⟨fun s => orbitQuartic ρ₀ s * f s, hstab, ?_⟩
    rw [carrierCharge_one_orbitQuartic_mul hre him hfa hford, hch]
    norm_num
  · exact ⟨f, hfC, hch⟩

/-- **The softness metatheorem.**  A class stable under orbit-quartic multiplication, with an
analytic finite-order member near every off-line off-real point, is soft: it plants nontrivial
charge everywhere off the line.  Softness is a closure property of the constraint, not an
accident of a particular witness. -/
theorem isSoft_of_orbitQuartic_stable {C : (ℂ → ℂ) → Prop}
    (hstab : ∀ ρ₀ : ℂ, ρ₀.re ≠ 1 / 2 → ρ₀.im ≠ 0 →
      ∀ f, C f → C (fun s => orbitQuartic ρ₀ s * f s))
    (hseed : ∀ ρ₀ : ℂ, ρ₀.re ≠ 1 / 2 → ρ₀.im ≠ 0 →
      ∃ f, C f ∧ AnalyticAt ℂ f ρ₀ ∧ analyticOrderAt f ρ₀ ≠ ⊤) :
    IsSoft C := by
  intro ρ₀ hre him
  obtain ⟨f, hfC, hfa, hford⟩ := hseed ρ₀ hre him
  exact carriesChargeAt_of_orbitQuartic_stable hre him hfC (hstab ρ₀ hre him f hfC) hfa hford

/-- No quartic-multiplication-stable class with analytic finite-order seeds forces RH-grade
parity: softness excludes the categorical cell, and parity-forcing IS the categorical cell. -/
theorem not_forcesRHParity_of_orbitQuartic_stable {C : (ℂ → ℂ) → Prop}
    (hstab : ∀ ρ₀ : ℂ, ρ₀.re ≠ 1 / 2 → ρ₀.im ≠ 0 →
      ∀ f, C f → C (fun s => orbitQuartic ρ₀ s * f s))
    (hseed : ∀ ρ₀ : ℂ, ρ₀.re ≠ 1 / 2 → ρ₀.im ≠ 0 →
      ∃ f, C f ∧ AnalyticAt ℂ f ρ₀ ∧ analyticOrderAt f ρ₀ ≠ ⊤) :
    ¬ ForcesRHParity C := by
  rw [forcesRHParity_iff_categorical]
  intro hcat
  exact hcat (plantsArbitrary_imp_carriesCharge (isSoft_of_orbitQuartic_stable hstab hseed))

/-! ### §3 The cut: classes containing ξ -/

/-- **The rigidity cut lies above multiplication stability.**  A constraint class containing ξ
that also contains ONE orbit-quartic multiple of ξ — at a single point beyond the wall, where ξ is
nonvanishing — cannot force RH-grade parity: the multiple carries charge `−1` there.  A constraint
able to decide the parity must therefore break stability under multiplication by FE-symmetric
polynomials, i.e. must read the coefficient/arithmetic structure of its members. -/
theorem not_forcesRHParity_of_xi_orbitQuartic_stable {C : (ℂ → ℂ) → Prop} (hxi : C xi)
    (hstab : C (fun s => orbitQuartic (2 + I) s * xi s)) :
    ¬ ForcesRHParity C := by
  intro hforce
  have h2re : (2 + I).re = 2 := by simp
  have h2im : (2 + I).im = 1 := by simp
  have hre : (2 + I).re ≠ 1 / 2 := by rw [h2re]; norm_num
  have him : (2 + I).im ≠ 0 := by rw [h2im]; norm_num
  have hxine : xi (2 + I) ≠ 0 := xi_ne_zero_of_one_le_re (by rw [h2re]; norm_num)
  have hval := hforce _ hstab (2 + I) hre
  rw [carrierCharge_one_orbitQuartic_mul hre him
      (xi_analyticOnNhd_univ _ (Set.mem_univ _)) (xi_orderAt_ne_top _),
    carrierCharge_one_eq_neg_one_pow,
    show analyticOrderAt xi (2 + I) = 0 from analyticOrderAt_eq_zero.mpr (Or.inr hxine)] at hval
  simp at hval

/-! ### §4 The monotone constraint lattice -/

/-- Realized charge is monotone in the constraint class. -/
theorem carriesChargeAt_mono {C C' : (ℂ → ℂ) → Prop} (h : ∀ f, C' f → C f) {ρ : ℂ}
    (hc : CarriesChargeAt C' ρ) : CarriesChargeAt C ρ := by
  obtain ⟨f, hf, hch⟩ := hc
  exact ⟨f, h f hf, hch⟩

/-- Parity-forcing descends along the constraint lattice: a subclass of a parity-forcing class is
parity-forcing. -/
theorem forcesRHParity_anti {C C' : (ℂ → ℂ) → Prop} (h : ∀ f, C' f → C f)
    (hforce : ForcesRHParity C) : ForcesRHParity C' :=
  fun f hf ρ hρ => hforce f (h f hf) ρ hρ

end RHTower
