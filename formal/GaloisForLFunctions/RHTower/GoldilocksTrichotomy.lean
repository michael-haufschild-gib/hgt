/-
The Goldilocks trichotomy: classifying candidate carrier classes by softness, categoricity, and the
Goldilocks middle.

A class `C : (ℂ → ℂ) → Prop` is tested by two properties phrased through the rung-1 deck charge
`carrierCharge f 1 ρ = (−1)^{ord_ρ f}` (`= 1` iff even/zero order, `≠ 1` iff an odd off-line zero):

* `PlantsArbitrary C` — at *every* off-line, off-real point some member carries a nontrivial charge
  (unbounded flexibility);
* `CarriesOffLineCharge C` — *some* off-line point carries a nontrivial charge.

The three cells partition every class (`goldilocks_trichotomy`, `trichotomy_disjoint`):

* **Soft** (`PlantsArbitrary`): too flexible — bump surgery plants an off-line odd zero anywhere, so
  the class cannot force RH-grade parity.  The FE + Schwarz class is soft (`feSchwarz_isSoft`), using
  the `V₄`-orbit witness `exists_feSchwarz_carrier_odd_charge`.
* **Categorical** (`¬ CarriesOffLineCharge`): no off-line charge at all. Witnessed by the singleton
  constant-one class (`const_isCategorical`). The separate `dirichlet_surgery_rigid` theorem
  excludes a polynomial multiplier of ζ; it does not place the Dirichlet-series class in this cell.
* **Goldilocks** (`CarriesOffLineCharge ∧ ¬ PlantsArbitrary`): charge-carrying yet rigid.  Nonempty —
  the single-zero class `{s ↦ s − ρ₀}` is Goldilocks (`linGap_isGoldilocks`).

`forcesRHParity_iff_categorical` is the payoff: forcing RH-grade parity by charge alone is *exactly*
the categorical collapse (no off-line charge).  The Goldilocks cell carries charge and does *not* force
parity by charge alone. A proposed additional conservation law needs its own definition and proof;
the taxonomy does not supply one. It also does not establish that only the middle cell can support
an arithmetic proof, or classify the ordinary Dirichlet-series class as a whole.
-/
import GaloisForLFunctions.RHTower.CarrierChargeSoftness
import GaloisForLFunctions.RHTower.DirichletRigidity

open Complex

namespace RHTower

/-! ### The three tests and the three cells -/

/-- A class carries nontrivial rung-1 charge at `ρ` if some member has odd order there. -/
def CarriesChargeAt (C : (ℂ → ℂ) → Prop) (ρ : ℂ) : Prop := ∃ f, C f ∧ carrierCharge f 1 ρ ≠ 1

/-- Test 1 (flexibility): the class can plant a nontrivial off-line charge at every off-line, off-real
point. -/
def PlantsArbitrary (C : (ℂ → ℂ) → Prop) : Prop :=
  ∀ ρ : ℂ, ρ.re ≠ 1 / 2 → ρ.im ≠ 0 → CarriesChargeAt C ρ

/-- Test 3 (charge): the class carries nontrivial off-line charge somewhere. -/
def CarriesOffLineCharge (C : (ℂ → ℂ) → Prop) : Prop :=
  ∃ ρ : ℂ, ρ.re ≠ 1 / 2 ∧ CarriesChargeAt C ρ

/-- The class forces RH-grade parity: every member has trivial charge at every off-line point. -/
def ForcesRHParity (C : (ℂ → ℂ) → Prop) : Prop :=
  ∀ f, C f → ∀ ρ : ℂ, ρ.re ≠ 1 / 2 → carrierCharge f 1 ρ = 1

/-- **Soft**: plants arbitrary off-line charge (too flexible). -/
def IsSoft (C : (ℂ → ℂ) → Prop) : Prop := PlantsArbitrary C
/-- **Categorical**: carries no off-line charge at all (collapsed/rigid). -/
def IsCategorical (C : (ℂ → ℂ) → Prop) : Prop := ¬ CarriesOffLineCharge C
/-- **Goldilocks**: carries off-line charge but cannot plant it arbitrarily. -/
def IsGoldilocks (C : (ℂ → ℂ) → Prop) : Prop := CarriesOffLineCharge C ∧ ¬ PlantsArbitrary C

theorem plantsArbitrary_imp_carriesCharge {C} (h : PlantsArbitrary C) : CarriesOffLineCharge C :=
  ⟨2 + I, by norm_num, h (2 + I) (by norm_num) (by norm_num)⟩

/-- **The Goldilocks trichotomy.**  Every candidate class is soft, Goldilocks, or categorical. -/
theorem goldilocks_trichotomy (C : (ℂ → ℂ) → Prop) :
    IsSoft C ∨ IsGoldilocks C ∨ IsCategorical C := by
  by_cases hp : PlantsArbitrary C
  · exact Or.inl hp
  · by_cases hc : CarriesOffLineCharge C
    · exact Or.inr (Or.inl ⟨hc, hp⟩)
    · exact Or.inr (Or.inr hc)

/-- The three cells are mutually exclusive. -/
theorem trichotomy_disjoint (C : (ℂ → ℂ) → Prop) :
    ¬ (IsSoft C ∧ IsGoldilocks C) ∧ ¬ (IsSoft C ∧ IsCategorical C) ∧
      ¬ (IsGoldilocks C ∧ IsCategorical C) :=
  ⟨fun ⟨hs, _, hng⟩ => hng hs, fun ⟨hs, hcat⟩ => hcat (plantsArbitrary_imp_carriesCharge hs),
    fun ⟨⟨hg, _⟩, hcat⟩ => hcat hg⟩

/-- **Forcing parity is exactly categorical collapse.**  A class forces RH-grade parity by charge iff
it carries no off-line charge: naive parity-forcing is the trivial (categorical) cell, and the
Goldilocks cell carries charge and does not force parity by charge alone — the seam input is what is
still missing. -/
theorem forcesRHParity_iff_categorical (C : (ℂ → ℂ) → Prop) :
    ForcesRHParity C ↔ IsCategorical C := by
  constructor
  · rintro hforce ⟨ρ, hre, f, hf, hne⟩; exact hne (hforce f hf ρ hre)
  · intro hcat f hf ρ hre
    by_contra hne
    exact hcat ⟨ρ, hre, f, hf, hne⟩

/-! ### The three cells, witnessed -/

/-- The FE + Schwarz carrier class: differentiable, functional-equation-symmetric, Schwarz-symmetric. -/
def FESchwarz (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ (∀ s, f (1 - s) = f s) ∧ (∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s))

/-- **Softness theorem (Deliverable 1).**  The FE + Schwarz class is soft: at every off-line, off-real
point it has a member with nontrivial charge — bump surgery on a `V₄`-orbit plants an off-line odd
zero while keeping both symmetries.  Hence the class cannot force RH-grade parity. -/
theorem feSchwarz_isSoft : IsSoft FESchwarz := by
  intro ρ hre him
  obtain ⟨f, hd, hfe, hconj, hc⟩ := exists_feSchwarz_carrier_odd_charge hre him
  exact ⟨f, ⟨hd, hfe, hconj⟩, by rw [hc]; norm_num⟩

theorem feSchwarz_not_forcesRHParity : ¬ ForcesRHParity FESchwarz := by
  rw [forcesRHParity_iff_categorical]
  exact fun hcat => hcat (plantsArbitrary_imp_carriesCharge feSchwarz_isSoft)

/-- Order of the linear carrier `s − ρ` at its zero is `1`. -/
theorem analyticOrderAt_linGap_self (ρ : ℂ) : analyticOrderAt (fun s => s - ρ) ρ = 1 := by
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - ρ) ρ := analyticAt_id.sub analyticAt_const
  refine hlin_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by simp) ?_
  have hd : deriv (fun s : ℂ => s - ρ) ρ = 1 := ((hasDerivAt_id ρ).sub_const ρ).deriv
  rw [hd]; exact one_ne_zero

/-- **Goldilocks theorem (Deliverable 3).**  The single-zero class `{s ↦ s − ρ₀}` carries nontrivial
off-line charge (an odd zero at `ρ₀`) but cannot plant it arbitrarily — at any other off-line point its
one member is nonzero, so its charge there is trivial.  It is Goldilocks: charge-carrying yet rigid.
The middle cell is nonempty. -/
theorem linGap_isGoldilocks : IsGoldilocks (fun f => f = fun s => s - (2 + I)) := by
  refine ⟨⟨2 + I, by norm_num, fun s => s - (2 + I), rfl, ?_⟩, ?_⟩
  · rw [carrierCharge_one_eq_neg_one_pow, analyticOrderAt_linGap_self]; norm_num
  · intro hpa
    obtain ⟨f, hf, hne⟩ := hpa (3 + I) (by norm_num) (by norm_num)
    subst hf
    apply hne
    have hord : analyticOrderAt (fun s : ℂ => s - (2 + I)) (3 + I) = 0 := by
      apply analyticOrderAt_eq_zero.mpr; right
      show (3 + I : ℂ) - (2 + I) ≠ 0; norm_num
    rw [carrierCharge_one_eq_neg_one_pow, hord]; norm_num

/-- **Categorical theorem (Deliverable 2), trivial witness.**  A nonvanishing (constant) class carries
no off-line charge — the collapsed/categorical cell. -/
theorem const_isCategorical : IsCategorical (fun f => f = fun _ => (1 : ℂ)) := by
  rintro ⟨ρ, _, f, hf, hne⟩
  subst hf
  apply hne
  have hord : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) ρ = 0 := by
    apply analyticOrderAt_eq_zero.mpr; right; norm_num
  rw [carrierCharge_one_eq_neg_one_pow, hord]; norm_num

/-- **Polynomial-multiplier obstruction.** No `P·ζ` with polynomial `P` of positive degree is an
ordinary Dirichlet series with finite absolute-convergence abscissa. This excludes the specified
planting operation and proves no categorical or general finite-divisor rigidity assertion. -/
theorem dirichlet_surgery_rigid {P : Polynomial ℂ} (hP : 0 < P.natDegree)
    {f : ℕ → ℂ} (hfa : LSeries.abscissaOfAbsConv f < ⊤) :
    ¬ (∀ᶠ x : ℝ in Filter.atTop, LSeries f (x : ℂ) = P.eval (x : ℂ) * riemannZeta (x : ℂ)) :=
  fun heq => no_polynomial_surgery_zeta hP hfa heq

end RHTower
