import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Splitting a multivariate power series ring along a partition of its variables

`MvPowerSeriesOptionSplit` peels off a single variable.  Splitting off a whole block at once is what
a deformation argument needs: the variables kept in the base and the variables deformed away form
two blocks, and the ring is the deformed block's power series ring over the kept block's.

## Main results

* `sumCons` — assembling an exponent on `σ ⊕ τ` from its two restrictions.
* `MvPowerSeries.sumEquiv` — the ring isomorphism
  `MvPowerSeries (σ ⊕ τ) A ≃+* MvPowerSeries τ (MvPowerSeries σ A)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ τ A : Type} [CommSemiring A]

/-- Assemble an exponent on `σ ⊕ τ` from its two restrictions. -/
def sumCons (m : σ →₀ ℕ) (d : τ →₀ ℕ) : σ ⊕ τ →₀ ℕ :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m, d)

@[simp] theorem sumCons_fst (m : σ →₀ ℕ) (d : τ →₀ ℕ) :
    (Finsupp.sumFinsuppAddEquivProdFinsupp (sumCons m d) : (σ →₀ ℕ) × (τ →₀ ℕ)).1 = m := by
  rw [sumCons, AddEquiv.apply_symm_apply]

@[simp] theorem sumCons_snd (m : σ →₀ ℕ) (d : τ →₀ ℕ) :
    (Finsupp.sumFinsuppAddEquivProdFinsupp (sumCons m d) : (σ →₀ ℕ) × (τ →₀ ℕ)).2 = d := by
  rw [sumCons, AddEquiv.apply_symm_apply]

@[simp] theorem sumCons_proj (e : σ ⊕ τ →₀ ℕ) :
    sumCons (Finsupp.sumFinsuppAddEquivProdFinsupp e).1
        (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 = e := by
  rw [sumCons]
  exact Finsupp.sumFinsuppAddEquivProdFinsupp.symm_apply_apply e

theorem sumCons_add (m₁ m₂ : σ →₀ ℕ) (d₁ d₂ : τ →₀ ℕ) :
    sumCons (m₁ + m₂) (d₁ + d₂) = sumCons m₁ d₁ + sumCons m₂ d₂ := by
  rw [sumCons, sumCons, sumCons, ← map_add]
  rfl

theorem sumCons_eq_zero_iff {m : σ →₀ ℕ} {d : τ →₀ ℕ} :
    sumCons m d = 0 ↔ m = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun e => (Finsupp.sumFinsuppAddEquivProdFinsupp e :
      (σ →₀ ℕ) × (τ →₀ ℕ))) h
    rw [sumCons, AddEquiv.apply_symm_apply, map_zero] at h1
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  · rintro ⟨rfl, rfl⟩
    rw [sumCons]
    exact map_zero _

/-- Split a multivariate power series along a partition of its variables. -/
def sumSplit (f : MvPowerSeries (σ ⊕ τ) A) : MvPowerSeries τ (MvPowerSeries σ A) :=
  fun d => (fun m => MvPowerSeries.coeff (sumCons m d) f : MvPowerSeries σ A)

/-- Reassemble a multivariate power series from its block expansion. -/
def sumJoin (g : MvPowerSeries τ (MvPowerSeries σ A)) : MvPowerSeries (σ ⊕ τ) A :=
  (fun e => MvPowerSeries.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp e).1
    (MvPowerSeries.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 g) :
      MvPowerSeries (σ ⊕ τ) A)

@[simp] theorem coeff_sumSplit (f : MvPowerSeries (σ ⊕ τ) A) (m : σ →₀ ℕ) (d : τ →₀ ℕ) :
    MvPowerSeries.coeff m (MvPowerSeries.coeff d (sumSplit f))
      = MvPowerSeries.coeff (sumCons m d) f := rfl

@[simp] theorem coeff_sumJoin (g : MvPowerSeries τ (MvPowerSeries σ A)) (e : σ ⊕ τ →₀ ℕ) :
    MvPowerSeries.coeff e (sumJoin g)
      = MvPowerSeries.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp e).1
          (MvPowerSeries.coeff (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 g) :=
  MvPowerSeries.coeff_apply _ e

theorem sumJoin_sumSplit (f : MvPowerSeries (σ ⊕ τ) A) : sumJoin (sumSplit f) = f := by
  ext e
  rw [coeff_sumJoin, coeff_sumSplit, sumCons_proj]

theorem sumSplit_sumJoin (g : MvPowerSeries τ (MvPowerSeries σ A)) : sumSplit (sumJoin g) = g := by
  ext d m
  rw [coeff_sumSplit, coeff_sumJoin, sumCons_fst, sumCons_snd]

theorem sumSplit_add (f g : MvPowerSeries (σ ⊕ τ) A) :
    sumSplit (f + g) = sumSplit f + sumSplit g := by
  ext d m
  simp

theorem sumSplit_one : sumSplit (1 : MvPowerSeries (σ ⊕ τ) A) = 1 := by
  classical
  ext d m
  rw [coeff_sumSplit, MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl, MvPowerSeries.coeff_one]
    by_cases hm : m = 0
    · subst hm
      rw [if_pos rfl, if_pos (sumCons_eq_zero_iff.mpr ⟨rfl, rfl⟩)]
    · rw [if_neg hm, if_neg]
      intro h
      exact hm (sumCons_eq_zero_iff.mp h).1
  · rw [if_neg hd, MvPowerSeries.coeff_zero, if_neg]
    intro h
    exact hd (sumCons_eq_zero_iff.mp h).2

theorem sumSplit_mul (f g : MvPowerSeries (σ ⊕ τ) A) :
    sumSplit (f * g) = sumSplit f * sumSplit g := by
  classical
  ext d m
  rw [coeff_sumSplit, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
  have hRHS : ∀ p ∈ Finset.antidiagonal d,
      MvPowerSeries.coeff m
          (MvPowerSeries.coeff p.1 (sumSplit f) * MvPowerSeries.coeff p.2 (sumSplit g))
        = ∑ q ∈ Finset.antidiagonal m,
            MvPowerSeries.coeff (sumCons q.1 p.1) f * MvPowerSeries.coeff (sumCons q.2 p.2) g := by
    intro p _
    rw [MvPowerSeries.coeff_mul]
    exact Finset.sum_congr rfl fun q _ => by rw [coeff_sumSplit, coeff_sumSplit]
  rw [Finset.sum_congr rfl hRHS]
  rw [← Finset.sum_product' (Finset.antidiagonal d) (Finset.antidiagonal m)
    (fun p q => MvPowerSeries.coeff (sumCons q.1 p.1) f * MvPowerSeries.coeff (sumCons q.2 p.2) g)]
  refine Finset.sum_nbij'
    (i := fun p : (σ ⊕ τ →₀ ℕ) × (σ ⊕ τ →₀ ℕ) =>
      ((( Finsupp.sumFinsuppAddEquivProdFinsupp p.1).2,
          (Finsupp.sumFinsuppAddEquivProdFinsupp p.2).2),
        ((Finsupp.sumFinsuppAddEquivProdFinsupp p.1).1,
          (Finsupp.sumFinsuppAddEquivProdFinsupp p.2).1)))
    (j := fun q : ((τ →₀ ℕ) × (τ →₀ ℕ)) × ((σ →₀ ℕ) × (σ →₀ ℕ)) =>
      (sumCons q.2.1 q.1.1, sumCons q.2.2 q.1.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_antidiagonal] at hp
    simp only [Finset.mem_product, Finset.mem_antidiagonal]
    have h := congrArg (fun e => (Finsupp.sumFinsuppAddEquivProdFinsupp e :
      (σ →₀ ℕ) × (τ →₀ ℕ))) hp
    rw [map_add] at h
    refine ⟨?_, ?_⟩
    · have h2 := congrArg Prod.snd h
      rw [Prod.snd_add, sumCons_snd] at h2
      exact h2
    · have h1 := congrArg Prod.fst h
      rw [Prod.fst_add, sumCons_fst] at h1
      exact h1
  · rintro ⟨⟨d₁, d₂⟩, ⟨m₁, m₂⟩⟩ hq
    simp only [Finset.mem_product, Finset.mem_antidiagonal] at hq
    simp only [Finset.mem_antidiagonal]
    rw [← sumCons_add, hq.1, hq.2]
  · rintro ⟨a, b⟩ _
    exact Prod.ext (sumCons_proj a) (sumCons_proj b)
  · rintro ⟨⟨d₁, d₂⟩, ⟨m₁, m₂⟩⟩ _
    exact Prod.ext (Prod.ext (sumCons_snd m₁ d₁) (sumCons_snd m₂ d₂))
      (Prod.ext (sumCons_fst m₁ d₁) (sumCons_fst m₂ d₂))
  · rintro ⟨a, b⟩ _
    rw [sumCons_proj, sumCons_proj]

/-- **Splitting a multivariate power series ring along a partition of its variables.** -/
def MvPowerSeries.sumEquiv (σ τ A : Type) [CommSemiring A] :
    MvPowerSeries (σ ⊕ τ) A ≃+* MvPowerSeries τ (MvPowerSeries σ A) where
  toFun := sumSplit
  invFun := sumJoin
  left_inv := sumJoin_sumSplit
  right_inv := sumSplit_sumJoin
  map_add' := sumSplit_add
  map_mul' := sumSplit_mul

@[simp] theorem constantCoeff_sumSplit (f : MvPowerSeries (σ ⊕ τ) A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.constantCoeff (sumSplit f))
      = MvPowerSeries.constantCoeff f := by
  have h := coeff_sumSplit f 0 0
  rw [sumCons_eq_zero_iff.mpr ⟨rfl, rfl⟩] at h
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using h

end

end GaloisForLFunctions.HTGeometry
