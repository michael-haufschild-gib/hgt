import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedLemma41Energy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIAmplitudeCover

namespace RHTower.Sieve

open Finset

noncomputable def matomakiTeravainenDirichletAmplitude
    (N : ℕ) (a : Fin N → ℂ) (t : ℝ) : ℝ :=
  ‖dirPoly N (sigmaWeightedCoeff N a 1) (-t)‖

theorem raisedDirichletValue_large_of_dirichletAmplitude_large
    {N A ell : ℕ} (hA : 1 ≤ A) (a : Fin N → ℂ) {rho t : ℝ}
    (hlarge : (A : ℝ) ^ (-rho) ≤ matomakiTeravainenDirichletAmplitude N a t) :
    (((A ^ ell : ℕ) : ℝ) ^ (-rho)) ≤
      ‖raisedDirichletValue N ell a 1 t‖ := by
  rw [raisedDirichletValue_eq_pow, norm_pow]
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) hlarge ell
  rw [matomakiTeravainenDirichletAmplitude] at hpow
  have hbase : (((A ^ ell : ℕ) : ℝ) ^ (-rho)) =
      ((A : ℝ) ^ (-rho)) ^ ell := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hA0]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA0]
    congr 1
    ring
  rw [hbase]
  exact hpow

theorem raisedDirichletValue_large_of_mem_matomakiTeravainenAmplitudeCell_left
    {S : Finset ℝ} {N A ell : ℕ} (hA : 1 < (A : ℝ))
    (a : Fin N → ℂ) {F₂ : ℝ → ℝ} {V₁ V₂ : ℝ} (hV₁ : 0 < V₁)
    {J₁ J₂ : ℕ} {ij : Fin J₁ × Fin J₂} {t : ℝ}
    (ht : t ∈ matomakiTeravainenAmplitudeCell S
      (matomakiTeravainenDirichletAmplitude N a) F₂ V₁ V₂ ij) :
    (((A ^ ell : ℕ) : ℝ) ^
      (-matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1)) ≤
        ‖raisedDirichletValue N ell a 1 t‖ := by
  have hlower : (2 : ℝ) ^ (ij.1 : ℕ) * V₁ ≤
      matomakiTeravainenDirichletAmplitude N a t := by
    exact (Finset.mem_filter.1 ht).2.1
  rw [← rpow_neg_matomakiTeravainenAmplitudeSigma hA hV₁] at hlower
  exact raisedDirichletValue_large_of_dirichletAmplitude_large
    (show 1 ≤ A by exact_mod_cast hA.le) a hlower

/-- The raised branch of Proposition 4.2 on one literal left-selected amplitude cell. -/
theorem exists_matomakiTeravainen_typeII_left_raised_cell_count_energy
    {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (kappa Q : ℝ)
        (a : Fin N → ℂ) (S : Finset ℝ) (F₂ : ℝ → ℝ)
        (V₁ V₂ : ℝ) (J₁ J₂ : ℕ) (ij : Fin J₁ × Fin J₂),
      T₀ ≤ T → 1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      1 < (A : ℝ) → 0 < ell →
      0 ≤ matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1 →
      0 < V₁ →
      (∀ r : Fin (ell + 1), 2 ≤ A ^ ell * 2 ^ (r : ℕ)) →
      (∀ r : Fin (ell + 1),
        T ^ ((9 : ℝ) / 11) ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ r : Fin (ell + 1),
        ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps)) →
      (∀ r : Fin (ell + 1),
        5 * eps ≤ huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ))
          (matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1) (ell + 1 : ℝ)) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ))
          (matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1) (ell + 1 : ℝ) ≤
            7 / 32 - 5 * eps) →
      (∀ r : Fin (ell + 1),
        2400 * Q ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
          ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
            (A ^ ell * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1)
            (ell + 1 : ℝ))) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ))
          (matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1) (ell + 1 : ℝ) ≤
            matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1 + kappa) →
      (∀ n : Fin N, a n ≠ 0 →
        A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A) →
      (∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
        Q * ((A ^ ell : ℕ) : ℝ)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (((matomakiTeravainenAmplitudeCell S
        (matomakiTeravainenDirichletAmplitude N a) F₂ V₁ V₂ ij).card : ℝ) ≤
        (ell + 1 : ℝ) * T ^
          (2 * (matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1 + kappa) -
            eps ^ 2 / 5)) := by
  obtain ⟨T₀, hT₀, hraised⟩ :=
    exists_lemma41_huxley_raised_energy heps hepss
  refine ⟨T₀, hT₀, ?_⟩
  intro T N A ell kappa Q a S F₂ V₁ V₂ J₁ J₂ ij hT hQ hQ3 hA hell
    hrho hV₁ hN hNlo hNhi hsl hsh hthr hcorr hsupp henergy hsep hspread
  let cell := matomakiTeravainenAmplitudeCell S
    (matomakiTeravainenDirichletAmplitude N a) F₂ V₁ V₂ ij
  apply hraised T N A ell
    (matomakiTeravainenAmplitudeSigma (A : ℝ) V₁ ij.1) kappa Q a cell
    hT hQ hQ3 (by exact_mod_cast hA.le) hell hrho hN hNlo hNhi hsl hsh hthr hcorr
    hsupp henergy
  · intro x hx y hy hxy
    exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy
  · intro x hx y hy
    exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1
  · intro t ht
    exact raisedDirichletValue_large_of_mem_matomakiTeravainenAmplitudeCell_left
      hA a hV₁ ht

theorem matomakiTeravainenAmplitudeCell_swap
    {α : Type*} [DecidableEq α] (S : Finset α) (F₁ F₂ : α → ℝ)
    (V₁ V₂ : ℝ) {J₁ J₂ : ℕ} (ij : Fin J₁ × Fin J₂) :
    matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂ ij =
      matomakiTeravainenAmplitudeCell S F₂ F₁ V₂ V₁ (ij.2, ij.1) := by
  ext q
  simp only [matomakiTeravainenAmplitudeCell, Finset.mem_filter]
  tauto

theorem raisedDirichletValue_large_of_mem_matomakiTeravainenAmplitudeCell_right
    {S : Finset ℝ} {N A ell : ℕ} (hA : 1 < (A : ℝ))
    (a : Fin N → ℂ) {F₁ : ℝ → ℝ} {V₁ V₂ : ℝ} (hV₂ : 0 < V₂)
    {J₁ J₂ : ℕ} {ij : Fin J₁ × Fin J₂} {t : ℝ}
    (ht : t ∈ matomakiTeravainenAmplitudeCell S F₁
      (matomakiTeravainenDirichletAmplitude N a) V₁ V₂ ij) :
    (((A ^ ell : ℕ) : ℝ) ^
      (-matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2)) ≤
        ‖raisedDirichletValue N ell a 1 t‖ := by
  have hlower : (2 : ℝ) ^ (ij.2 : ℕ) * V₂ ≤
      matomakiTeravainenDirichletAmplitude N a t := by
    exact (Finset.mem_filter.1 ht).2.2.2.1
  rw [← rpow_neg_matomakiTeravainenAmplitudeSigma hA hV₂] at hlower
  exact raisedDirichletValue_large_of_dirichletAmplitude_large
    (show 1 ≤ A by exact_mod_cast hA.le) a hlower

/-- Symmetric right-selected branch of Proposition 4.2 on one literal amplitude cell. -/
theorem exists_matomakiTeravainen_typeII_right_raised_cell_count_energy
    {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (kappa Q : ℝ)
        (a : Fin N → ℂ) (S : Finset ℝ) (F₁ : ℝ → ℝ)
        (V₁ V₂ : ℝ) (J₁ J₂ : ℕ) (ij : Fin J₁ × Fin J₂),
      T₀ ≤ T → 1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      1 < (A : ℝ) → 0 < ell →
      0 ≤ matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2 →
      0 < V₂ →
      (∀ r : Fin (ell + 1), 2 ≤ A ^ ell * 2 ^ (r : ℕ)) →
      (∀ r : Fin (ell + 1),
        T ^ ((9 : ℝ) / 11) ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ r : Fin (ell + 1),
        ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps)) →
      (∀ r : Fin (ell + 1),
        5 * eps ≤ huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ))
          (matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2) (ell + 1 : ℝ)) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ))
          (matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2) (ell + 1 : ℝ) ≤
            7 / 32 - 5 * eps) →
      (∀ r : Fin (ell + 1),
        2400 * Q ≤ ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
          ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
            (A ^ ell * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2)
            (ell + 1 : ℝ))) →
      (∀ r : Fin (ell + 1),
        huxleyThresholdLossSigma
          (A ^ ell * 2 ^ (r : ℕ))
          (matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2) (ell + 1 : ℝ) ≤
            matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2 + kappa) →
      (∀ n : Fin N, a n ≠ 0 →
        A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A) →
      (∑ j : Fin (N ^ ell), ‖convPow N ell a j‖ ^ 2 ≤
        Q * ((A ^ ell : ℕ) : ℝ)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (((matomakiTeravainenAmplitudeCell S F₁
        (matomakiTeravainenDirichletAmplitude N a) V₁ V₂ ij).card : ℝ) ≤
        (ell + 1 : ℝ) * T ^
          (2 * (matomakiTeravainenAmplitudeSigma (A : ℝ) V₂ ij.2 + kappa) -
            eps ^ 2 / 5)) := by
  obtain ⟨T₀, hT₀, hleft⟩ :=
    exists_matomakiTeravainen_typeII_left_raised_cell_count_energy heps hepss
  refine ⟨T₀, hT₀, ?_⟩
  intro T N A ell kappa Q a S F₁ V₁ V₂ J₁ J₂ ij hT hQ hQ3 hA hell
    hrho hV₂ hN hNlo hNhi hsl hsh hthr hcorr hsupp henergy hsep hspread
  have hcount := hleft T N A ell kappa Q a S F₁ V₂ V₁ J₂ J₁ (ij.2, ij.1)
    hT hQ hQ3 hA hell hrho hV₂ hN hNlo hNhi hsl hsh hthr hcorr
    hsupp henergy hsep hspread
  rw [← matomakiTeravainenAmplitudeCell_swap S F₁
    (matomakiTeravainenDirichletAmplitude N a) V₁ V₂ ij] at hcount
  exact hcount

/-- Proposition 4.2's two-factor branch selection supplies every active-cell count. The old
abstract `hcount` premise is replaced by the literal coefficient energies and Huxley range checks
for the selected factor. -/
theorem exists_matomakiTeravainen_typeII_actual_cell_counts_energy
    {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ ell₁ : ℕ) (kappa₁ Q₁ : ℝ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ ell₂ : ℕ) (kappa₂ Q₂ : ℝ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ) (V₁ V₂ C : ℝ) (J₁ J₂ : ℕ),
      T₀ ≤ T →
      1 ≤ Q₁ → Q₁ ^ 3 ≤ T ^ (eps ^ 2) →
      1 ≤ Q₂ → Q₂ ^ 3 ≤ T ^ (eps ^ 2) →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      0 < ell₁ → 0 < ell₂ → 0 < V₁ → 0 < V₂ →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₁ a₁ q ≤ 1) →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₂ a₂ q ≤ 1) →
      (∀ r : Fin (ell₁ + 1), 2 ≤ A₁ ^ ell₁ * 2 ^ (r : ℕ)) →
      (∀ r : Fin (ell₁ + 1),
        T ^ ((9 : ℝ) / 11) ≤ ((A₁ ^ ell₁ * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ r : Fin (ell₁ + 1),
        ((A₁ ^ ell₁ * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps)) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        ∀ r : Fin (ell₁ + 1),
          5 * eps ≤ huxleyThresholdLossSigma
            (A₁ ^ ell₁ * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
            (ell₁ + 1 : ℝ)) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        ∀ r : Fin (ell₁ + 1),
          huxleyThresholdLossSigma
            (A₁ ^ ell₁ * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
            (ell₁ + 1 : ℝ) ≤ 7 / 32 - 5 * eps) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        ∀ r : Fin (ell₁ + 1),
          2400 * Q₁ ≤ ((A₁ ^ ell₁ * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
            ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
              (A₁ ^ ell₁ * 2 ^ (r : ℕ))
              (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
              (ell₁ + 1 : ℝ))) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        ∀ r : Fin (ell₁ + 1),
          huxleyThresholdLossSigma
            (A₁ ^ ell₁ * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
            (ell₁ + 1 : ℝ) ≤
              matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 + kappa₁) →
      (∀ r : Fin (ell₂ + 1), 2 ≤ A₂ ^ ell₂ * 2 ^ (r : ℕ)) →
      (∀ r : Fin (ell₂ + 1),
        T ^ ((9 : ℝ) / 11) ≤ ((A₂ ^ ell₂ * 2 ^ (r : ℕ) : ℕ) : ℝ)) →
      (∀ r : Fin (ell₂ + 1),
        ((A₂ ^ ell₂ * 2 ^ (r : ℕ) : ℕ) : ℝ) ≤ T ^ (1 - eps)) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        ∀ r : Fin (ell₂ + 1),
          5 * eps ≤ huxleyThresholdLossSigma
            (A₂ ^ ell₂ * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2)
            (ell₂ + 1 : ℝ)) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        ∀ r : Fin (ell₂ + 1),
          huxleyThresholdLossSigma
            (A₂ ^ ell₂ * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2)
            (ell₂ + 1 : ℝ) ≤ 7 / 32 - 5 * eps) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        ∀ r : Fin (ell₂ + 1),
          2400 * Q₂ ≤ ((A₂ ^ ell₂ * 2 ^ (r : ℕ) : ℕ) : ℝ) ^
            ((1 : ℝ) / 2 - 2 * huxleyThresholdLossSigma
              (A₂ ^ ell₂ * 2 ^ (r : ℕ))
              (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2)
              (ell₂ + 1 : ℝ))) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        ∀ r : Fin (ell₂ + 1),
          huxleyThresholdLossSigma
            (A₂ ^ ell₂ * 2 ^ (r : ℕ))
            (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2)
            (ell₂ + 1 : ℝ) ≤
              matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 + kappa₂) →
      (∀ n : Fin N₁, a₁ n ≠ 0 →
        A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∑ j : Fin (N₁ ^ ell₁), ‖convPow N₁ ell₁ a₁ j‖ ^ 2 ≤
        Q₁ * ((A₁ ^ ell₁ : ℕ) : ℝ)) →
      (∀ n : Fin N₂, a₂ n ≠ 0 →
        A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∑ j : Fin (N₂ ^ ell₂), ‖convPow N₂ ell₂ a₂ j‖ ^ 2 ≤
        Q₂ * ((A₂ ^ ell₂ : ℕ) : ℝ)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      0 ≤ C → (ell₁ + 1 : ℝ) ≤ C → (ell₂ + 1 : ℝ) ≤ C →
      2 * kappa₁ ≤ eps ^ 2 / 10 → 2 * kappa₂ ≤ eps ^ 2 / 10 →
      ∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        ((matomakiTeravainenAmplitudeCell S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij).card : ℝ) ≤
            C * T ^
              (2 * min
                (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
                (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) -
                eps ^ 2 / 10) := by
  obtain ⟨T₀, hT₀, hraised⟩ := exists_lemma41_huxley_raised_energy heps hepss
  refine ⟨T₀, hT₀, ?_⟩
  intro T N₁ A₁ ell₁ kappa₁ Q₁ a₁ N₂ A₂ ell₂ kappa₂ Q₂ a₂ S V₁ V₂ C J₁ J₂
    hT hQ₁ hQ₁3 hQ₂ hQ₂3 hA₁ hA₂ hell₁ hell₂ hV₁ hV₂ hF₁one hF₂one
    hblock₁ hNlo₁ hNhi₁ hsl₁ hsh₁ hthr₁ hcorr₁
    hblock₂ hNlo₂ hNhi₂ hsl₂ hsh₂ hthr₂ hcorr₂
    hsupp₁ henergy₁ hsupp₂ henergy₂ hsep hspread hC hellC₁ hellC₂ hkappa₁ hkappa₂
    ij hij
  have hT1 : 1 ≤ T := hT₀.trans hT
  have hrho := active_matomakiTeravainenAmplitudeSigma_nonneg
    hA₁ hA₂ hV₁ hV₂ hF₁one hF₂one hij
  by_cases hside :
      matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2
  · let cell := matomakiTeravainenAmplitudeCell S
      (matomakiTeravainenDirichletAmplitude N₁ a₁)
      (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij
    have hc := hraised T N₁ A₁ ell₁
      (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
      kappa₁ Q₁ a₁ cell hT hQ₁ hQ₁3 (by exact_mod_cast hA₁.le) hell₁ hrho.1
      hblock₁ hNlo₁ hNhi₁ (hsl₁ ij hij hside) (hsh₁ ij hij hside)
      (hthr₁ ij hij hside) (hcorr₁ ij hij hside) hsupp₁ henergy₁
      (by
        intro x hx y hy hxy
        exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
      (by
        intro x hx y hy
        exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
      (by
        intro t ht
        exact raisedDirichletValue_large_of_mem_matomakiTeravainenAmplitudeCell_left
          hA₁ a₁ hV₁ ht)
    calc
      ((matomakiTeravainenAmplitudeCell S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij).card : ℝ)
          ≤ (ell₁ + 1 : ℝ) * T ^
              (2 * (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 + kappa₁) -
                eps ^ 2 / 5) := hc
      _ ≤ C * T ^
          (2 * min
            (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
            (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) -
            eps ^ 2 / 10) := by
        apply mul_le_mul hellC₁
        · apply Real.rpow_le_rpow_of_exponent_le hT1
          rw [min_eq_left hside]
          linarith
        · positivity
        · exact hC
  · have hside' :
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 := lt_of_not_ge hside
    let cell := matomakiTeravainenAmplitudeCell S
      (matomakiTeravainenDirichletAmplitude N₁ a₁)
      (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij
    have hc := hraised T N₂ A₂ ell₂
      (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2)
      kappa₂ Q₂ a₂ cell hT hQ₂ hQ₂3 (by exact_mod_cast hA₂.le) hell₂ hrho.2
      hblock₂ hNlo₂ hNhi₂ (hsl₂ ij hij hside') (hsh₂ ij hij hside')
      (hthr₂ ij hij hside') (hcorr₂ ij hij hside') hsupp₂ henergy₂
      (by
        intro x hx y hy hxy
        exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
      (by
        intro x hx y hy
        exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
      (by
        intro t ht
        exact raisedDirichletValue_large_of_mem_matomakiTeravainenAmplitudeCell_right
          hA₂ a₂ hV₂ ht)
    calc
      ((matomakiTeravainenAmplitudeCell S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij).card : ℝ)
          ≤ (ell₂ + 1 : ℝ) * T ^
              (2 * (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 + kappa₂) -
                eps ^ 2 / 5) := hc
      _ ≤ C * T ^
          (2 * min
            (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
            (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) -
            eps ^ 2 / 10) := by
        apply mul_le_mul hellC₂
        · apply Real.rpow_le_rpow_of_exponent_le hT1
          rw [min_eq_right hside'.le]
          linarith
        · positivity
        · exact hC

end RHTower.Sieve
