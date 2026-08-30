import GaloisForLFunctions.HTGeometry.RittShiftRigidity

/-!
# From a first-order equation to Ritt's form

A *Ritt frame* is a field extension `K → L` carrying a ring endomorphism `σ` compatible with an
endomorphism `ψ` of the base, a derivation `d` compatible with a derivation of the base, and a
chain-rule factor `ρ` in the base with `d ∘ σ = ρ · (σ ∘ d)`.  This is the algebraic shape of the
substitution `f ↦ f ∘ R` acting on germs at a fixed point of `R`, with `ρ = R′`.

Let `τ` solve the linearizing equation `σ τ = q · τ` with `q` a derivation constant.  Then `d τ`
solves `σ (d τ) = (q / ρ) · d τ`, so `τ` and `d τ` are two multiplicative shift coordinates.  If
they are algebraically dependent over the base — that is, if `τ` satisfies an algebraic differential
equation of order one — then multiplicative rigidity produces integers `r ≠ 0`, `j` and a base
element `A` with

`(d τ) ^ r = A · τ ^ j`,

which is the differential equation Ritt singles out for differentially algebraic Poincaré
functions.  The degenerate case in which the integer vector has no `d τ` component is closed by
taking the logarithmic derivative of the resulting monomial relation.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A difference–differential frame over a base field. -/
structure RittFrame (K L : Type*) [Field K] [Field L] [Algebra K L] where
  /-- The shift on the extension. -/
  σ : L →+* L
  /-- The shift on the base. -/
  ψ : K →+* K
  /-- The derivation on the extension. -/
  d : L → L
  /-- The derivation on the base. -/
  dK : K → K
  /-- The chain-rule factor. -/
  ρ : K
  comp : ∀ a : K, σ (algebraMap K L a) = algebraMap K L (ψ a)
  fixed : ∀ y : L, σ y = y → ∃ a : K, algebraMap K L a = y
  d_add : ∀ x y : L, d (x + y) = d x + d y
  d_mul : ∀ x y : L, d (x * y) = d x * y + x * d y
  d_base : ∀ a : K, d (algebraMap K L a) = algebraMap K L (dK a)
  ρ_ne : ρ ≠ 0
  chain : ∀ x : L, d (σ x) = algebraMap K L ρ * σ (d x)

namespace RittFrame

variable (Fr : RittFrame K L)

theorem d_zero : Fr.d 0 = 0 := by
  have h := Fr.d_add 0 0
  simp only [add_zero] at h
  linear_combination -h

/-- The power rule for the frame's derivation. -/
theorem d_pow_succ (x : L) : ∀ n : ℕ, Fr.d (x ^ (n + 1)) = ((n : L) + 1) * x ^ n * Fr.d x
  | 0 => by simp
  | (n + 1) => by
      have hx : x ^ (n + 2) = x * x ^ (n + 1) := by ring
      rw [hx, Fr.d_mul, d_pow_succ x n]
      push_cast
      ring

/-- The derivative of a solution of the linearizing equation is again a multiplicative shift
coordinate, with the multiplier divided by the chain-rule factor. -/
theorem sigma_d_eq_of_shift {τ : L} {q : K} (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (Fr.d τ) = algebraMap K L (q / Fr.ρ) * Fr.d τ := by
  have hρ : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr Fr.ρ_ne
  have h1 : Fr.d (Fr.σ τ) = algebraMap K L q * Fr.d τ := by
    rw [hshift, Fr.d_mul, Fr.d_base, hqconst, map_zero, zero_mul, zero_add]
  have h2 := Fr.chain τ
  rw [h1] at h2
  have h3 : algebraMap K L Fr.ρ * Fr.σ (Fr.d τ) = algebraMap K L q * Fr.d τ := h2.symm
  rw [map_div₀]
  field_simp
  linear_combination h3

end RittFrame

/-- **Ritt's first-order form.**  If the linearizer `τ` and its derivative are algebraically
dependent over the base — an algebraic differential equation of order one — then `τ` satisfies
`(d τ) ^ r = A · τ ^ j` with `r ≠ 0` and `A` a nonzero base element. -/
theorem exists_rittForm_of_not_algebraicIndependent [CharZero K] (Fr : RittFrame K L)
    {τ : L} {q : K} (hτ : τ ≠ 0) (hq : q ≠ 0) (hdτ : Fr.d τ ≠ 0) (hqconst : Fr.dK q = 0)
    (hshift : Fr.σ τ = algebraMap K L q * τ)
    (hdep : ¬ AlgebraicIndependent K ![τ, Fr.d τ]) :
    ∃ (r j : ℤ) (A : K), r ≠ 0 ∧ A ≠ 0 ∧ (Fr.d τ) ^ r = algebraMap K L A * τ ^ j := by
  classical
  have hshift' := Fr.sigma_d_eq_of_shift hqconst hshift
  have hqρ : q / Fr.ρ ≠ 0 := div_ne_zero hq Fr.ρ_ne
  have hy : ∀ i : Fin 2, (![τ, Fr.d τ] : Fin 2 → L) i ≠ 0 := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hτ, hdτ⟩
  have hqq : ∀ i : Fin 2, (![q, q / Fr.ρ] : Fin 2 → K) i ≠ 0 := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hq, hqρ⟩
  have hsh : ∀ i : Fin 2, Fr.σ ((![τ, Fr.d τ] : Fin 2 → L) i)
      = algebraMap K L ((![q, q / Fr.ρ] : Fin 2 → K) i) * (![τ, Fr.d τ] : Fin 2 → L) i := by
    rw [Fin.forall_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨hshift, hshift'⟩
  obtain ⟨m, hm, a, ha⟩ :=
    exists_algebraMap_eq_zpow_prod_of_not_algebraicIndependent Fr.σ Fr.ψ Fr.comp Fr.fixed
      ![τ, Fr.d τ] ![q, q / Fr.ρ] hy hqq hsh hdep
  rw [Fin.prod_univ_two] at ha
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ha
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact (mul_ne_zero (zpow_ne_zero _ hτ) (zpow_ne_zero _ hdτ)) ha.symm
  by_cases hm1 : m 1 = 0
  · -- no derivative component: differentiate the resulting monomial relation
    have hm0 : m 0 ≠ 0 := by
      intro h0
      exact hm (funext fun i => by fin_cases i <;> simpa using ‹_›)
    rw [hm1, zpow_zero, mul_one] at ha
    obtain ⟨n, hn, b, hb0, hb⟩ :
        ∃ n : ℕ, 0 < n ∧ ∃ b : K, b ≠ 0 ∧ algebraMap K L b = τ ^ n := by
      rcases lt_or_gt_of_ne hm0 with hlt | hgt
      · refine ⟨(-m 0).toNat, by omega, a⁻¹, inv_ne_zero ha0, ?_⟩
        rw [map_inv₀, ha, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg]
      · exact ⟨(m 0).toNat, by omega, a, ha0,
          by rw [ha, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]⟩
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
    have hkK : ((k : K) + 1) ≠ 0 := by
      rw [show ((k : K) + 1) = ((k + 1 : ℕ) : K) by push_cast; ring]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hcast : algebraMap K L ((k : K) + 1) = (k : L) + 1 := by
      rw [map_add, map_natCast, map_one]
    have hkL : algebraMap K L ((k : K) + 1) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr hkK
    have hbL : algebraMap K L b ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hb0
    have hd : algebraMap K L (Fr.dK b) = ((k : L) + 1) * τ ^ k * Fr.d τ := by
      rw [← Fr.d_base, hb, Fr.d_pow_succ]
    have hkey : algebraMap K L ((k : K) + 1) * algebraMap K L b * Fr.d τ
        = algebraMap K L (Fr.dK b) * τ := by
      calc algebraMap K L ((k : K) + 1) * algebraMap K L b * Fr.d τ
          = ((k : L) + 1) * τ ^ (k + 1) * Fr.d τ := by rw [hb, hcast]
        _ = (((k : L) + 1) * τ ^ k * Fr.d τ) * τ := by ring
        _ = algebraMap K L (Fr.dK b) * τ := by rw [hd]
    set A : K := Fr.dK b / (((k : K) + 1) * b) with hA
    have hrel : Fr.d τ = algebraMap K L A * τ := by
      rw [hA, map_div₀, map_mul]
      field_simp
      linear_combination hkey
    refine ⟨1, 1, A, one_ne_zero, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero, zero_mul] at hrel
      exact hdτ hrel
    · rw [zpow_one, zpow_one, hrel]
  · exact ⟨m 1, -m 0, a, hm1, ha0, by rw [ha, zpow_neg]; field_simp⟩

end GaloisForLFunctions.HTGeometry
