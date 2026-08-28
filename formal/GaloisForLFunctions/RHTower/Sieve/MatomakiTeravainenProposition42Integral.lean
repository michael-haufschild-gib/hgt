import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIProposition42
import GaloisForLFunctions.HTGeometry.CellMaxSetDiscretisation

/-!
# Proposition 4.2 in integral form

`exists_matomakiTeravainen_typeII_proposition42_huxley` bounds the Type-II amplitude energy over a
finite one-spaced frequency **set** whose points all satisfy the amplitude threshold.  The paper
states the same estimate as an integral over an arbitrary subset `U` of the ordinate range.

The passage is the cell-max discretisation restricted to a closed set
(`HTGeometry/CellMaxSetDiscretisation.exists_spaced_families_setIntegral_le`): each unit cell meets
`U` in a compact set, a continuous integrand attains its maximum there at a point *of `U`*, and
splitting the cells by parity produces two one-spaced families inside `U`.  The cost is a factor
two.

The restricting set is closed for free: the Dirichlet amplitude is a continuous function of the
ordinate, so every threshold condition on it cuts out a closed set.

* `continuous_matomakiTeravainenDirichletAmplitude` (from the corpus's `continuous_dirPoly`);
* `isClosed_matomakiTeravainenTypeIIRegion` — the Proposition 4.2 region is closed;
* `exists_matomakiTeravainen_typeII_proposition42_integral`.
-/

namespace RHTower.Sieve

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Dirichlet amplitude is a continuous function of the ordinate. -/
theorem continuous_matomakiTeravainenDirichletAmplitude (N : ℕ) (a : Fin N → ℂ) :
    Continuous (matomakiTeravainenDirichletAmplitude N a) := by
  have h : matomakiTeravainenDirichletAmplitude N a
      = fun t : ℝ => ‖dirPoly N (sigmaWeightedCoeff N a 1) (-t)‖ := rfl
  rw [h]
  exact continuous_norm.comp ((continuous_dirPoly N _).comp continuous_neg)

/-- The Proposition 4.2 region: the ordinates in a window at which both amplitudes are at most one,
the first is at most `B₁`, and at least one of them exceeds its threshold. -/
def matomakiTeravainenTypeIIRegion (T : ℝ) (N₁ : ℕ) (a₁ : Fin N₁ → ℂ) (N₂ : ℕ)
    (a₂ : Fin N₂ → ℂ) (A₁ A₂ : ℕ) (sigma₀ B₁ : ℝ) : Set ℝ :=
  {t | t ∈ Set.Icc (-T) T}
    ∩ {t | matomakiTeravainenDirichletAmplitude N₁ a₁ t ≤ 1}
    ∩ {t | matomakiTeravainenDirichletAmplitude N₂ a₂ t ≤ 1}
    ∩ {t | matomakiTeravainenDirichletAmplitude N₁ a₁ t ≤ B₁}
    ∩ ({t | (A₁ : ℝ) ^ (-sigma₀) ≤ matomakiTeravainenDirichletAmplitude N₁ a₁ t}
        ∪ {t | (A₂ : ℝ) ^ (-sigma₀) ≤ matomakiTeravainenDirichletAmplitude N₂ a₂ t})

theorem isClosed_matomakiTeravainenTypeIIRegion (T : ℝ) {N₁ : ℕ} (a₁ : Fin N₁ → ℂ) {N₂ : ℕ}
    (a₂ : Fin N₂ → ℂ) (A₁ A₂ : ℕ) (sigma₀ B₁ : ℝ) :
    IsClosed (matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ sigma₀ B₁) := by
  have h₁ := continuous_matomakiTeravainenDirichletAmplitude N₁ a₁
  have h₂ := continuous_matomakiTeravainenDirichletAmplitude N₂ a₂
  refine IsClosed.inter (IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_) ?_
  · exact isClosed_Icc
  · exact isClosed_le h₁ continuous_const
  · exact isClosed_le h₂ continuous_const
  · exact isClosed_le h₁ continuous_const
  · exact IsClosed.union (isClosed_le continuous_const h₁) (isClosed_le continuous_const h₂)

theorem matomakiTeravainenTypeIIRegion_subset_Icc (T : ℝ) {N₁ : ℕ} (a₁ : Fin N₁ → ℂ) {N₂ : ℕ}
    (a₂ : Fin N₂ → ℂ) (A₁ A₂ : ℕ) (sigma₀ B₁ : ℝ) :
    matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ sigma₀ B₁ ⊆ Set.Icc (-T) T :=
  fun _ ht => ht.1.1.1.1

/-- **Proposition 4.2 in integral form.**  The Type-II amplitude energy integrated over the closed
region where both amplitudes are at most one, the first is at most `B₁`, and at least one exceeds
its threshold, obeys twice the bound of the finite one-spaced form. -/
theorem exists_matomakiTeravainen_typeII_proposition42_integral
    {eps mu eta sigma₀ Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (heta : 0 < eta)
    (hcap : sigma₀ + eta + eps ^ 2 / 20 ≤ 7 / 32 - 5 * eps)
    (hCprod : 1 ≤ Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (k w₁ w₂ : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (B₁ : ℝ),
      T₀ ≤ T →
      1 ≤ N₁ → N₁ ≤ 2 * A₁ →
      1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      T ^ mu ≤ (A₁ : ℝ) →
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * eps) →
      T / (Cprod * (1 + |Real.log T|) ^ k) ≤ (A₁ : ℝ) * (A₂ : ℝ) →
      (A₁ : ℝ) * (A₂ : ℝ) ≤ T * (Cprod * (1 + |Real.log T|) ^ k) →
      (∀ n : Fin N₁,
        ‖a₁ n‖ ≤ C₁ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₁)) →
      (∀ n : Fin N₂,
        ‖a₂ n‖ ≤ C₂ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₂)) →
      (∀ n : Fin N₁, a₁ n ≠ 0 →
        A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∀ n : Fin N₂, a₂ n ≠ 0 →
        A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∫ t in matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ sigma₀ B₁,
          matomakiTeravainenDirichletAmplitude N₁ a₁ t ^ 2 *
            matomakiTeravainenDirichletAmplitude N₂ a₂ t ^ 2)
        ≤ 2 * (16384 * B₁ ^ 2 * (1 + |Real.log T|) * C₂ ^ 2 *
              (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w₂ + 1)) - 1)
            + T ^ (-(eps ^ 2 / 20)) + T ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨T₀, hT₀, hfin⟩ :=
    exists_matomakiTeravainen_typeII_proposition42_huxley heps hepss hmu hmulo hmuhi heta hcap
      hCprod hC₁ hC₂ k w₁ w₂
  refine ⟨T₀, hT₀, ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ B₁ hT hN₁ hN₁A hN₂ hN₂A hA₁ hA₂ hmuA hA₁hi hprodlo hprodhi
    hcoef₁ hcoef₂ hsupp₁ hsupp₂
  set U : Set ℝ := matomakiTeravainenTypeIIRegion T N₁ a₁ N₂ a₂ A₁ A₂ sigma₀ B₁ with hU
  set F : ℝ → ℝ := fun t => matomakiTeravainenDirichletAmplitude N₁ a₁ t ^ 2 *
    matomakiTeravainenDirichletAmplitude N₂ a₂ t ^ 2 with hF
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one (le_trans hT₀ hT)
  have hFcont : Continuous F := by
    refine Continuous.mul ?_ ?_
    · exact ((continuous_matomakiTeravainenDirichletAmplitude N₁ a₁).pow 2)
    · exact ((continuous_matomakiTeravainenDirichletAmplitude N₂ a₂).pow 2)
  have hF0 : ∀ t, 0 ≤ F t := by
    intro t
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hUclosed : IsClosed U := isClosed_matomakiTeravainenTypeIIRegion T a₁ a₂ A₁ A₂ sigma₀ B₁
  have hUIcc : U ⊆ Set.Icc (-T) T :=
    matomakiTeravainenTypeIIRegion_subset_Icc T a₁ a₂ A₁ A₂ sigma₀ B₁
  set m : ℕ := ⌈2 * T⌉₊ + 3 with hm
  have hmge : 2 * T + 3 ≤ (m : ℝ) := by
    have := Nat.le_ceil (2 * T)
    push_cast [hm]
    linarith
  obtain ⟨S₁, S₂, hS₁sub, hS₂sub, hS₁sep, hS₂sep, hdisc⟩ :=
    exists_spaced_families_setIntegral_le hFcont hF0 hUclosed (-T - 1) 1 one_pos m
  -- the window covers the region
  have hcover : U ∩ Set.Ioc (-T - 1) (-T - 1 + (m : ℝ) * 1) = U := by
    refine Set.inter_eq_left.mpr fun t ht => ?_
    have h := hUIcc ht
    rw [Set.mem_Icc] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hcover] at hdisc
  -- the hypotheses of the finite form, for either family
  have hfam : ∀ S : Finset ℝ, (↑S ⊆ U ∩ Set.Icc (-T - 1) (-T - 1 + (m : ℝ) * 1)) →
      (∀ t ∈ S, ∀ u ∈ S, t ≠ u → (1 : ℝ) ≤ |t - u|) →
      ∑ q ∈ S, F q
        ≤ 16384 * B₁ ^ 2 * (1 + |Real.log T|) * C₂ ^ 2 *
            (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w₂ + 1)) - 1)
          + T ^ (-(eps ^ 2 / 20)) + T ^ (-(1 : ℝ) / 2) := by
    intro S hSsub hSsep
    have hSU : ∀ q ∈ S, q ∈ U := fun q hq => (hSsub (Finset.mem_coe.mpr hq)).1
    refine hfin T N₁ A₁ a₁ N₂ A₂ a₂ S B₁ hT hN₁ hN₁A hN₂ hN₂A hA₁ hA₂ hmuA hA₁hi hprodlo
      hprodhi hcoef₁ hcoef₂ hsupp₁ hsupp₂ ?_ ?_ ?_ hSsep ?_ ?_
    · exact fun q hq => (hSU q hq).1.1.1.2
    · exact fun q hq => (hSU q hq).1.1.2
    · exact fun q hq => (hSU q hq).2
    · intro x hx y hy
      have hx' := hUIcc (hSU x hx)
      have hy' := hUIcc (hSU y hy)
      rw [Set.mem_Icc] at hx' hy'
      rw [abs_le]
      constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
    · exact fun q hq => (hSU q hq).1.2
  have h₁ := hfam S₁ hS₁sub hS₁sep
  have h₂ := hfam S₂ hS₂sub hS₂sep
  refine hdisc.trans ?_
  rw [one_mul]
  linarith [h₁, h₂]

end

end RHTower.Sieve
