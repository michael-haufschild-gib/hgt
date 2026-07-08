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
import GaloisForLFunctions.RHTower.WeightMismatchRefutation
import GaloisForLFunctions.RHTower.Reflection

noncomputable section

namespace RHTower

open Complex

/-! ### §1 The parity toggle -/

/-- Multiplying by the orbit quartic raises the vanishing order at its simple zero by one. -/
theorem analyticOrderAt_orbitQuartic_mul {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0)
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f ρ₀) :
    analyticOrderAt (fun s => orbitQuartic ρ₀ s * f s) ρ₀ = 1 + analyticOrderAt f ρ₀ := by
  have h := analyticOrderAt_mul ((orbitQuartic_differentiable ρ₀).analyticAt ρ₀) hf
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

/-- **The rigidity cut lies above multiplication stability.**  A constraint class containing ONE
orbit-quartic multiple of ξ — at a single point beyond the wall, where ξ is nonvanishing — cannot
force RH-grade parity: the multiple carries charge `−1` there.  In particular no
multiplication-stable class containing ξ forces parity.  A constraint able to decide the parity
must therefore break stability under multiplication by FE-symmetric polynomials, i.e. must read
the coefficient/arithmetic structure of its members. -/
theorem not_forcesRHParity_of_xi_orbitQuartic_stable {C : (ℂ → ℂ) → Prop}
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
  norm_num at hval

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

/-! ### §5 The rigidity endpoint: parity-forcing of the ξ-scalar class is the base rung -/

/-- The real-scalar class of ξ — the constraint lattice's rigid endpoint, where the class has
collapsed to the object itself. -/
def XiScalarClass (f : ℂ → ℂ) : Prop := ∃ c : ℝ, f = fun s => (c : ℂ) * xi s

/-- **The two ends of the constraint lattice meet at the base rung.**  Parity-forcing of the
ξ-scalar class is EXACTLY the first RH-ladder rung: every real multiple of ξ has trivial charge at
every off-line point iff every right-half ξ-order is even.  Left-half points transport across the
critical line by the FE and reality pairings of orders; scalars do not move the order.  Together
with the softness metatheorem this squeezes class-level parity laws to nothing: below this class,
stability under one quartic multiplication already destroys forcing; at this class, forcing IS the
rung. -/
theorem forcesRHParity_xiScalarClass_iff_rhLadder_one :
    ForcesRHParity XiScalarClass ↔ RHLadder 1 := by
  rw [rhLadder_one_iff_even_order]
  constructor
  · intro hforce ρ hρ hzero
    have hre : ρ.re ≠ 1 / 2 := by
      have := mem_rightHalf.mp hρ
      linarith
    have hch := hforce xi ⟨1, by funext s; rw [Complex.ofReal_one, one_mul]⟩ ρ hre
    rw [even_iff_two_dvd]
    have hdvd := (carrierCharge_eq_one_iff_dvd xi 1 ρ).mp hch
    rwa [pow_one] at hdvd
  · intro heven f hf ρ hre
    obtain ⟨c, rfl⟩ := hf
    by_cases hc : c = 0
    · subst hc
      rw [carrierCharge_one_eq_neg_one_pow,
        show analyticOrderAt (fun s => (((0 : ℝ) : ℂ)) * xi s) ρ = ⊤ from
          analyticOrderAt_eq_top.mpr (Filter.Eventually.of_forall fun _ => by simp),
        ENat.toNat_top, pow_zero]
    · have hcC : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
      have hord : analyticOrderAt (fun s => ((c : ℝ) : ℂ) * xi s) ρ = analyticOrderAt xi ρ := by
        have h := analyticOrderAt_mul (analyticAt_const (v := ((c : ℝ) : ℂ)) (x := ρ))
          (xi_analyticOnNhd_univ ρ (Set.mem_univ ρ))
        rw [show ((fun _ => ((c : ℝ) : ℂ)) * xi) = (fun s => ((c : ℝ) : ℂ) * xi s) from rfl] at h
        rw [h, show analyticOrderAt (fun _ : ℂ => ((c : ℝ) : ℂ)) ρ = 0 from
          analyticOrderAt_eq_zero.mpr (Or.inr hcC), zero_add]
      rw [carrierCharge_one_eq_neg_one_pow, hord]
      have heven' : Even (analyticOrderAt xi ρ).toNat := by
        by_cases hzero : xi ρ = 0
        · by_cases hhalf : 1 / 2 < ρ.re
          · exact heven ρ (mem_rightHalf.mpr hhalf) hzero
          · have hordrefl : analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) =
                analyticOrderAt xi ρ := by
              rw [xi_orderAt_one_sub, xi_orderAt_conj]
            have hlt : ρ.re < 1 / 2 := lt_of_le_of_ne (not_lt.mp hhalf) hre
            have hmem : 1 - (starRingEnd ℂ) ρ ∈ rightHalf := by
              rw [mem_rightHalf]
              simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
              linarith
            have hzrefl : xi (1 - (starRingEnd ℂ) ρ) = 0 := by
              have hne : analyticOrderAt xi (1 - (starRingEnd ℂ) ρ) ≠ 0 := by
                rw [hordrefl]
                exact analyticOrderAt_ne_zero.mpr
                  ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hzero⟩
              exact (analyticOrderAt_ne_zero.mp hne).2
            have hev := heven _ hmem hzrefl
            rwa [hordrefl] at hev
        · rw [analyticOrderAt_eq_zero.mpr (Or.inr hzero)]
          simp
      exact heven'.neg_one_pow

/-- **No class-level shortcut to the rung.**  Any parity-forcing constraint class containing ξ
already certifies the base rung, because forcing instantiates at ξ itself.  Locating a
parity-forcing class around ξ is therefore never easier than the rung — combined with the
softness metatheorem, class-level parity laws are squeezed to nothing: below multiplication
stability they are impossible, and wherever they hold they were the rung all along. -/
theorem rhLadder_one_of_forcesRHParity {C : (ℂ → ℂ) → Prop} (hxi : C xi)
    (hforce : ForcesRHParity C) : RHLadder 1 := by
  rw [rhLadder_one_iff_even_order]
  intro ρ hρ hzero
  have hre : ρ.re ≠ 1 / 2 := by
    have := mem_rightHalf.mp hρ
    linarith
  have hch := hforce xi hxi ρ hre
  rw [even_iff_two_dvd]
  have hdvd := (carrierCharge_eq_one_iff_dvd xi 1 ρ).mp hch
  rwa [pow_one] at hdvd

/-! ### §6 The full ladder: level-`k` charge laws collapse the same way -/

/-- **No class-level shortcut at any level.**  A constraint class containing ξ whose members all
have trivial level-`k` charge off the line certifies the level-`k` ladder rung directly: forcing
instantiates at ξ.  The class-level collapse is ladder-uniform, not a parity accident. -/
theorem rhLadder_of_forces_charge_level {C : (ℂ → ℂ) → Prop} (hxi : C xi) {k : ℕ}
    (hforce : ∀ f, C f → ∀ ρ : ℂ, ρ.re ≠ 1 / 2 → carrierCharge f k ρ = 1) :
    RHLadder k := by
  intro ρ hρ _
  have hre : ρ.re ≠ 1 / 2 := by
    have := mem_rightHalf.mp hρ
    linarith
  exact (carrierCharge_eq_one_iff_enat_dvd (xi_orderAt_ne_top ρ)).mp (hforce xi hxi ρ hre)

/-- **The toggle defeats every level at once.**  In a class stable under one orbit-quartic
multiplication, the member and its multiple have consecutive vanishing orders at the quartic's
zero, and consecutive integers are never both `2^k`-divisible at a positive level: one of the two
carries nontrivial level-`k` charge.  Class-level divisibility laws fail below multiplication
stability at EVERY rung simultaneously. -/
theorem exists_nontrivial_charge_level_of_orbitQuartic_stable {C : (ℂ → ℂ) → Prop} {ρ₀ : ℂ}
    (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) {f : ℂ → ℂ} (hfC : C f)
    (hstab : C (fun s => orbitQuartic ρ₀ s * f s))
    (hfa : AnalyticAt ℂ f ρ₀) (hford : analyticOrderAt f ρ₀ ≠ ⊤)
    {k : ℕ} (hk : k ≠ 0) :
    ∃ g, C g ∧ carrierCharge g k ρ₀ ≠ 1 := by
  by_cases hdvd : 2 ^ k ∣ (analyticOrderAt f ρ₀).toNat
  · refine ⟨fun s => orbitQuartic ρ₀ s * f s, hstab, ?_⟩
    simp only [ne_eq, carrierCharge_eq_one_iff_dvd]
    rw [analyticOrderAt_orbitQuartic_mul hre him hfa, ENat.toNat_add (by simp) hford]
    intro hdvd'
    have h1 : 2 ^ k ∣ 1 := (Nat.dvd_add_right hdvd).mp (by rwa [Nat.add_comm] at hdvd')
    have h2 : 2 ^ k = 1 := Nat.eq_one_of_dvd_one h1
    exact hk (by
      by_contra hk0
      have := Nat.one_lt_two_pow_iff.mpr hk0
      omega)
  · refine ⟨f, hfC, ?_⟩
    simp only [ne_eq, carrierCharge_eq_one_iff_dvd]
    exact hdvd

end RHTower
