import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Splitting one variable off a multivariate power series

`MvPolynomial.optionEquivLeft` separates a distinguished variable of a multivariate polynomial;
mathlib has no power-series counterpart.  The identification is what lets an iterated one-variable
Hensel lift be compared with a multivariate one: both live in the same ring once a variable is
split off, so a root is determined by its constant term regardless of the order in which the
variables were deformed.

## Main results

* `optionCons` — assembling an `Option σ` exponent from a natural number and a `σ` exponent.
* `MvPowerSeries.optionEquivLeft` — the ring isomorphism
  `MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- Assemble an exponent on `Option σ` from its value at `none` and its restriction to `σ`. -/
def optionCons (n : ℕ) (d : σ →₀ ℕ) : Option σ →₀ ℕ :=
  Finsupp.optionEquiv.symm (n, d)

@[simp] theorem optionCons_none (n : ℕ) (d : σ →₀ ℕ) : optionCons n d none = n := by
  classical
  simp [optionCons, Finsupp.optionEquiv, Finsupp.update_apply]

@[simp] theorem some_optionCons (n : ℕ) (d : σ →₀ ℕ) :
    Finsupp.some (optionCons n d) = d := by
  simp [optionCons, Finsupp.optionEquiv]

@[simp] theorem optionCons_none_some (e : Option σ →₀ ℕ) :
    optionCons (e none) (Finsupp.some e) = e := by
  have := Finsupp.optionEquiv.symm_apply_apply e
  rwa [Finsupp.optionEquiv_apply] at this

theorem optionCons_add (n₁ n₂ : ℕ) (d₁ d₂ : σ →₀ ℕ) :
    optionCons (n₁ + n₂) (d₁ + d₂) = optionCons n₁ d₁ + optionCons n₂ d₂ := by
  classical
  ext a
  cases a with
  | none => simp
  | some a =>
      have h : ∀ (n : ℕ) (d : σ →₀ ℕ), optionCons n d (some a) = d a := by
        intro n d
        have := Finsupp.some_apply (optionCons n d) a
        rw [some_optionCons] at this
        exact this.symm
      simp [h]

theorem optionCons_injective : Function.Injective (fun p : ℕ × (σ →₀ ℕ) => optionCons p.1 p.2) := by
  intro p q hpq
  have h1 : p.1 = q.1 := by
    have := congrArg (fun e : Option σ →₀ ℕ => e none) hpq
    simpa using this
  have h2 : p.2 = q.2 := by
    have := congrArg (fun e : Option σ →₀ ℕ => Finsupp.some e) hpq
    simpa using this
  exact Prod.ext h1 h2

theorem some_add (a b : Option σ →₀ ℕ) :
    Finsupp.some (a + b) = Finsupp.some a + Finsupp.some b := by
  ext x
  simp [Finsupp.some_apply]

theorem optionCons_eq_zero_iff {n : ℕ} {d : σ →₀ ℕ} : optionCons n d = 0 ↔ n = 0 ∧ d = 0 := by
  constructor
  · intro h
    constructor
    · have := congrArg (fun e : Option σ →₀ ℕ => e none) h
      simpa using this
    · have := congrArg Finsupp.some h
      simpa using this
  · rintro ⟨rfl, rfl⟩
    ext a
    cases a with
    | none => simp
    | some a =>
        have h := Finsupp.some_apply (optionCons (0 : ℕ) (0 : σ →₀ ℕ)) a
        rw [some_optionCons] at h
        rw [← h]
        simp

/-- Split off the distinguished variable of a multivariate power series. -/
def optionSplit (f : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  PowerSeries.mk fun n => (fun d => MvPowerSeries.coeff (optionCons n d) f : MvPowerSeries σ R)

/-- Reassemble a multivariate power series from its expansion in the distinguished variable. -/
def optionJoin (g : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  (fun e => MvPowerSeries.coeff (Finsupp.some e) (PowerSeries.coeff (e none) g) :
    MvPowerSeries (Option σ) R)

@[simp] theorem coeff_optionSplit (f : MvPowerSeries (Option σ) R) (n : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (PowerSeries.coeff n (optionSplit f))
      = MvPowerSeries.coeff (optionCons n d) f := by
  rw [optionSplit, PowerSeries.coeff_mk, MvPowerSeries.coeff_apply]

@[simp] theorem coeff_optionJoin (g : PowerSeries (MvPowerSeries σ R)) (e : Option σ →₀ ℕ) :
    MvPowerSeries.coeff e (optionJoin g)
      = MvPowerSeries.coeff (Finsupp.some e) (PowerSeries.coeff (e none) g) :=
  MvPowerSeries.coeff_apply _ e

theorem optionJoin_optionSplit (f : MvPowerSeries (Option σ) R) :
    optionJoin (optionSplit f) = f := by
  ext e
  rw [coeff_optionJoin, coeff_optionSplit, optionCons_none_some]

theorem optionSplit_optionJoin (g : PowerSeries (MvPowerSeries σ R)) :
    optionSplit (optionJoin g) = g := by
  ext n d
  rw [coeff_optionSplit, coeff_optionJoin, optionCons_none, some_optionCons]

theorem optionSplit_add (f g : MvPowerSeries (Option σ) R) :
    optionSplit (f + g) = optionSplit f + optionSplit g := by
  ext n d
  simp

theorem optionSplit_one : optionSplit (1 : MvPowerSeries (Option σ) R) = 1 := by
  classical
  ext n d
  rw [coeff_optionSplit, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, MvPowerSeries.coeff_one]
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl, if_pos (optionCons_eq_zero_iff.mpr ⟨rfl, rfl⟩)]
    · rw [if_neg hd, if_neg]
      intro h
      exact hd (optionCons_eq_zero_iff.mp h).2
  · rw [if_neg hn, MvPowerSeries.coeff_zero, if_neg]
    intro h
    exact hn (optionCons_eq_zero_iff.mp h).1

theorem optionSplit_mul (f g : MvPowerSeries (Option σ) R) :
    optionSplit (f * g) = optionSplit f * optionSplit g := by
  classical
  ext n d
  rw [coeff_optionSplit, MvPowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  have hRHS : ∀ p ∈ Finset.antidiagonal n,
      MvPowerSeries.coeff d
          (PowerSeries.coeff p.1 (optionSplit f) * PowerSeries.coeff p.2 (optionSplit g))
        = ∑ q ∈ Finset.antidiagonal d,
            MvPowerSeries.coeff (optionCons p.1 q.1) f *
              MvPowerSeries.coeff (optionCons p.2 q.2) g := by
    intro p _
    rw [MvPowerSeries.coeff_mul]
    exact Finset.sum_congr rfl fun q _ => by rw [coeff_optionSplit, coeff_optionSplit]
  rw [Finset.sum_congr rfl hRHS]
  rw [← Finset.sum_product' (Finset.antidiagonal n) (Finset.antidiagonal d)
    (fun p q => MvPowerSeries.coeff (optionCons p.1 q.1) f *
      MvPowerSeries.coeff (optionCons p.2 q.2) g)]
  refine Finset.sum_nbij'
    (i := fun p : (Option σ →₀ ℕ) × (Option σ →₀ ℕ) =>
      ((p.1 none, p.2 none), (Finsupp.some p.1, Finsupp.some p.2)))
    (j := fun q : (ℕ × ℕ) × ((σ →₀ ℕ) × (σ →₀ ℕ)) =>
      (optionCons q.1.1 q.2.1, optionCons q.1.2 q.2.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_product, Finset.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · have := congrArg (fun e : Option σ →₀ ℕ => e none) hp
      simpa using this
    · have := congrArg Finsupp.some hp
      rw [some_add, some_optionCons] at this
      exact this
  · rintro ⟨⟨n₁, n₂⟩, ⟨d₁, d₂⟩⟩ hq
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at hq
    simp only [Finset.mem_antidiagonal]
    rw [← optionCons_add, hq.1, hq.2]
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨⟨n₁, n₂⟩, ⟨d₁, d₂⟩⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp

/-- **Splitting off one variable of a multivariate power series ring.** -/
def MvPowerSeries.optionEquivLeft (σ : Type*) (R : Type*) [CommSemiring R] :
    MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := optionSplit
  invFun := optionJoin
  left_inv := optionJoin_optionSplit
  right_inv := optionSplit_optionJoin
  map_add' := optionSplit_add
  map_mul' := optionSplit_mul

@[simp] theorem MvPowerSeries.optionEquivLeft_apply (f : MvPowerSeries (Option σ) R) :
    MvPowerSeries.optionEquivLeft σ R f = optionSplit f := rfl

@[simp] theorem constantCoeff_optionJoin (g : PowerSeries (MvPowerSeries σ R)) :
    MvPowerSeries.constantCoeff (optionJoin g)
      = MvPowerSeries.constantCoeff (PowerSeries.constantCoeff g) := by
  have h := coeff_optionJoin g 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff] at h
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_zero_eq_constantCoeff]
    using h

@[simp] theorem constantCoeff_optionSplit (f : MvPowerSeries (Option σ) R) :
    MvPowerSeries.constantCoeff (PowerSeries.constantCoeff (optionSplit f))
      = MvPowerSeries.constantCoeff f := by
  have h := coeff_optionSplit f 0 0
  rw [optionCons_eq_zero_iff.mpr ⟨rfl, rfl⟩] at h
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_zero_eq_constantCoeff]
    using h

end

end GaloisForLFunctions.HTGeometry
