import GaloisForLFunctions.HTGeometry.RittFirstOrderForm
import GaloisForLFunctions.HTGeometry.RittHomogeneousBaseRelation

/-!
# The pure-eigen case of a tower collapse

When the collapse relation of the jet tower has no lower-order coefficients, the top jet is a pure
multiplicative shift coordinate, with multiplier `q / ρ^n`.  It and the linearizer are then two
multiplicative shift coordinates, so multiplicative rigidity turns any algebraic dependence between
them into a monomial relation with base coefficients:

`a = τ^{m₀} · (d^[n] τ)^{m₁}`,   `(m₀, m₁) ≠ 0`,  `a ≠ 0`.

For `n = 1` this is the step that produces Ritt's first-order form; for higher `n` it is the same
rigidity applied one level up the tower.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **A pure eigen relation at level `n` gives a monomial relation.** -/
theorem exists_monomial_of_pure_jet_eigen (Fr : RittFrame K L)
    {τ : L} {q : K} {n : ℕ} (hτ : τ ≠ 0) (hq : q ≠ 0) (hjet : Fr.d^[n] τ ≠ 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (heig : Fr.σ (Fr.d^[n] τ) = algebraMap K L (q / Fr.ρ ^ n) * Fr.d^[n] τ)
    (hdep : ¬ AlgebraicIndependent K ![τ, Fr.d^[n] τ]) :
    ∃ (m : Fin 2 → ℤ) (a : K), m ≠ 0 ∧ a ≠ 0 ∧
      algebraMap K L a = τ ^ (m 0) * (Fr.d^[n] τ) ^ (m 1) := by
  classical
  have hqn : q / Fr.ρ ^ n ≠ 0 := div_ne_zero hq (pow_ne_zero n Fr.ρ_ne)
  have hy : ∀ i : Fin 2, (![τ, Fr.d^[n] τ] : Fin 2 → L) i ≠ 0 := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hτ, hjet⟩
  have hqq : ∀ i : Fin 2, (![q, q / Fr.ρ ^ n] : Fin 2 → K) i ≠ 0 := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hq, hqn⟩
  have hsh : ∀ i : Fin 2, Fr.σ ((![τ, Fr.d^[n] τ] : Fin 2 → L) i)
      = algebraMap K L ((![q, q / Fr.ρ ^ n] : Fin 2 → K) i)
        * (![τ, Fr.d^[n] τ] : Fin 2 → L) i := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hshift, heig⟩
  obtain ⟨m, hm, a, ha⟩ :=
    exists_algebraMap_eq_zpow_prod_of_not_algebraicIndependent Fr.σ Fr.ψ Fr.comp Fr.fixed
      ![τ, Fr.d^[n] τ] ![q, q / Fr.ρ ^ n] hy hqq hsh hdep
  rw [Fin.prod_univ_two] at ha
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
  refine ⟨m, a, hm, ?_, ha⟩
  intro h0
  rw [h0, map_zero] at ha
  exact (mul_ne_zero (zpow_ne_zero _ hτ) (zpow_ne_zero _ hjet)) ha.symm

/-- **The pure-eigen case always yields Ritt's first-order form.**  Applying the shift to the
monomial relation turns it into a homogeneous base relation whose exponent pair cannot vanish,
because the derivative exponent enters the chain-rule factor with weight `n`. -/
theorem rittForm_of_pure_jet_eigen [CharZero K] (Fr : RittFrame K L)
    {τ : L} {q : K} {n : ℕ} (hn : 0 < n) (hτ : τ ≠ 0) (hq : q ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (hjet : Fr.d^[n] τ ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (heig : Fr.σ (Fr.d^[n] τ) = algebraMap K L (q / Fr.ρ ^ n) * Fr.d^[n] τ)
    (hdep : ¬ AlgebraicIndependent K ![τ, Fr.d^[n] τ]) :
    ∃ (r j : ℤ) (A : K), r ≠ 0 ∧ A ≠ 0 ∧ (Fr.d τ) ^ r = algebraMap K L A * τ ^ j := by
  obtain ⟨m, a, hm, ha0, ha⟩ :=
    exists_monomial_of_pure_jet_eigen Fr hτ hq hjet hshift heig hdep
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hqn : q / Fr.ρ ^ n ≠ 0 := div_ne_zero hq (pow_ne_zero n hρ0)
  -- apply the shift to the monomial relation
  have hsh := congrArg Fr.σ ha
  rw [Fr.comp, map_mul, map_zpow₀, map_zpow₀, hshift, heig, mul_zpow, mul_zpow] at hsh
  have hqLne : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq
  have hρLne : algebraMap K L Fr.ρ ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hbase : Fr.ψ a = q ^ (m 0 + m 1) * Fr.ρ ^ (-(n : ℤ) * m 1) * a := by
    have hqL : algebraMap K L (q ^ (m 0 + m 1) * Fr.ρ ^ (-(n : ℤ) * m 1))
        = algebraMap K L q ^ (m 0) * (algebraMap K L (q / Fr.ρ ^ n)) ^ (m 1) := by
      rw [map_mul, map_zpow₀, map_zpow₀, map_div₀, map_pow, div_zpow, zpow_mul,
        zpow_neg, zpow_natCast, zpow_add₀ hqLne]
      field_simp
      rw [← mul_zpow, one_div, inv_mul_cancel₀ (pow_ne_zero n hρLne), one_zpow]
    refine (algebraMap K L).injective ?_
    rw [map_mul, hqL, ha]
    linear_combination hsh
  have him : (m 0 + m 1) ≠ 0 ∨ (-(n : ℤ) * m 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hm1 : m 1 = 0 := by
      have hnz : (-(n : ℤ)) ≠ 0 := by
        simp only [neg_ne_zero, Nat.cast_ne_zero]
        omega
      exact (mul_eq_zero.mp h2).resolve_left hnz
    have hm0 : m 0 = 0 := by omega
    exact hm (funext fun i => by fin_cases i <;> simpa using ‹_›)
  exact exists_rittForm_of_homogeneous_base_relation Fr hτ hdτ hq hqconst hshift ha0 him hbase

end GaloisForLFunctions.HTGeometry
