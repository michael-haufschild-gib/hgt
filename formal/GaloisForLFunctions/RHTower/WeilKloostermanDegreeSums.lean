import Mathlib

/-!
# Kloosterman weights on monic polynomials: degree sums

Over a finite field `F`, monic polynomials of degree `m` are parametrized by their lower coefficients
(`monicOf`, `monicDeg`). The Kloosterman weight `λ(f) = ψ(-nextCoeff f - a·f'(0)/f(0))` (zero when
`f(0) = 0`) is multiplicative on monic polynomials, and its degree sums are
`s₀ = 1`, `s₁ = K(a) = Σ_{x≠0} ψ(x + a/x)`, `s₂ = q` (ψ primitive, `a ≠ 0`), `s_m = 0` for `m ≥ 3`.
These are the coefficients of the L-function `1 + K(a) T + q T²` of the Kloosterman sum: step 1 of the
elementary proof of Weil's bound (card `weil-bound-kloosterman-lean`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.WeilKloosterman

variable {F : Type*} [Field F]

/-- The monic polynomial `X^m + Σ_{i<m} c_i X^i`. -/
noncomputable def monicOf (m : ℕ) (c : Fin m → F) : F[X] :=
  X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ)

theorem monicOf_coeff (m : ℕ) (c : Fin m → F) (k : ℕ) :
    (monicOf m c).coeff k = if h : k < m then c ⟨k, h⟩ else if k = m then 1 else 0 := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hk : k < m
  · have hne : k ≠ m := by omega
    rw [dif_pos hk, if_neg hne, zero_add, Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro b _ hb
      have : k ≠ (b : ℕ) := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  · rw [dif_neg hk, Finset.sum_eq_zero, add_zero]
    intro b _
    have : k ≠ (b : ℕ) := by omega
    simp [this]

theorem monicOf_natDegree_le (m : ℕ) (c : Fin m → F) : (monicOf m c).natDegree ≤ m := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have h1 : ¬ k < m := by
    have : m < k := by exact_mod_cast hk
    omega
  have h2 : k ≠ m := by
    have : m < k := by exact_mod_cast hk
    omega
  rw [monicOf_coeff, dif_neg h1, if_neg h2]

theorem monicOf_coeff_self (m : ℕ) (c : Fin m → F) : (monicOf m c).coeff m = 1 := by
  rw [monicOf_coeff]; simp

theorem monicOf_monic (m : ℕ) (c : Fin m → F) : (monicOf m c).Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one m (monicOf_natDegree_le m c)
    (monicOf_coeff_self m c)

theorem monicOf_natDegree (m : ℕ) (c : Fin m → F) : (monicOf m c).natDegree = m :=
  Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (monicOf_natDegree_le m c)
    (by rw [monicOf_coeff_self]; exact one_ne_zero)

theorem monicOf_injective (m : ℕ) : Function.Injective (monicOf (F := F) m) := by
  intro c d h
  funext i
  have := congrArg (fun f => f.coeff i) h
  simpa [monicOf_coeff, i.isLt] using this

theorem monicOf_surj {f : F[X]} (hf : f.Monic) :
    f = monicOf f.natDegree (fun i => f.coeff i) := by
  ext k
  rw [monicOf_coeff]
  split_ifs with h1 h2
  · rfl
  · subst h2; exact hf.coeff_natDegree
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]; omega

variable [Fintype F] [DecidableEq F]

/-- Monic polynomials of degree `m`. -/
noncomputable def monicDeg (m : ℕ) : Finset F[X] := univ.image (monicOf (F := F) m)

theorem mem_monicDeg {m : ℕ} {f : F[X]} : f ∈ monicDeg m ↔ f.Monic ∧ f.natDegree = m := by
  constructor
  · intro h
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨monicOf_monic m c, monicOf_natDegree m c⟩
  · rintro ⟨hf, rfl⟩
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (monicOf_surj hf).symm⟩

theorem sum_monicDeg {M : Type*} [AddCommMonoid M] (m : ℕ) (g : F[X] → M) :
    ∑ f ∈ monicDeg m, g f = ∑ c : Fin m → F, g (monicOf m c) :=
  Finset.sum_image (fun _ _ _ _ h => monicOf_injective m h)

theorem card_monicDeg (m : ℕ) : (monicDeg (F := F) m).card = Fintype.card F ^ m := by
  rw [monicDeg, Finset.card_image_of_injective _ (monicOf_injective m), Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin]

omit [Fintype F] [DecidableEq F] in
theorem monicOf_nextCoeff {m : ℕ} (hm : 1 ≤ m) (c : Fin m → F) :
    (monicOf m c).nextCoeff = c ⟨m - 1, by omega⟩ := by
  rw [Polynomial.nextCoeff, monicOf_natDegree, if_neg (by omega), monicOf_coeff,
    dif_pos (by omega)]

section weight
variable (ψ : AddChar F ℂ) (a : F)

omit [Fintype F] [DecidableEq F] in
theorem coeff_one_mul (f g : F[X]) :
    (f * g).coeff 1 = f.coeff 1 * g.coeff 0 + f.coeff 0 * g.coeff 1 := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]
  simp
  ring

/-- Kloosterman weight, zero on polynomials vanishing at `0`. -/
noncomputable def klW (f : F[X]) : ℂ :=
  if f.coeff 0 = 0 then 0 else ψ (-f.nextCoeff - a * (f.coeff 1 / f.coeff 0))

omit [Fintype F] in
theorem klW_mul {f g : F[X]} (hf : f.Monic) (hg : g.Monic) :
    klW ψ a (f * g) = klW ψ a f * klW ψ a g := by
  unfold klW
  rw [mul_coeff_zero]
  by_cases hf0 : f.coeff 0 = 0
  · simp [hf0]
  by_cases hg0 : g.coeff 0 = 0
  · simp [hg0]
  rw [if_neg (mul_ne_zero hf0 hg0), if_neg hf0, if_neg hg0, ← AddChar.map_add_eq_mul,
    hf.nextCoeff_mul hg, coeff_one_mul]
  congr 1
  field_simp
  ring

/-- The Kloosterman sum `K(a) = Σ_{x ≠ 0} ψ(x + a/x)`. -/
noncomputable def kloosterman : ℂ := ∑ x : F, if x = 0 then 0 else ψ (x + a / x)

/-- Degree sums of the Kloosterman weight. -/
noncomputable def degSum (m : ℕ) : ℂ := ∑ f ∈ monicDeg m, klW ψ a f

theorem degSum_zero : degSum ψ a 0 = 1 := by
  rw [degSum, sum_monicDeg]
  simp [klW, monicOf_coeff, Polynomial.nextCoeff, monicOf_natDegree]

theorem degSum_one : degSum ψ a 1 = kloosterman ψ a := by
  rw [degSum, sum_monicDeg, kloosterman]
  rw [← (Equiv.funUnique (Fin 1) F).symm.sum_comp]
  have h : ∀ x : F, klW ψ a (monicOf 1 ((Equiv.funUnique (Fin 1) F).symm x)) =
      if x = 0 then 0 else ψ (-x - a * (1 / x)) := by
    intro x
    have hn : (monicOf 1 ((Equiv.funUnique (Fin 1) F).symm x)).nextCoeff = x := by
      rw [monicOf_nextCoeff le_rfl]; rfl
    simp only [klW, hn, monicOf_coeff]
    simp
  simp_rw [h]
  refine Fintype.sum_equiv (Equiv.neg F) _ _ (fun x => ?_)
  simp only [Equiv.neg_apply, neg_eq_zero]
  split_ifs
  · rfl
  · congr 1; field_simp; ring

theorem degSum_two (hψ : ψ.IsPrimitive) (ha : a ≠ 0) :
    degSum ψ a 2 = Fintype.card F := by
  rw [degSum, sum_monicDeg, ← (finTwoArrowEquiv F).symm.sum_comp, Fintype.sum_prod_type]
  have h : ∀ c0 c1 : F, klW ψ a (monicOf 2 ((finTwoArrowEquiv F).symm (c0, c1))) =
      if c0 = 0 then 0 else ψ (c1 * (-1 - a / c0)) := by
    intro c0 c1
    have hn : (monicOf 2 ((finTwoArrowEquiv F).symm (c0, c1))).nextCoeff = c1 := by
      rw [monicOf_nextCoeff (by norm_num)]; rfl
    simp only [klW, hn, monicOf_coeff]
    simp
    split_ifs
    · rfl
    · congr 1; field_simp
  simp_rw [h]
  have hin : ∀ c0 : F, (∑ c1 : F, if c0 = 0 then (0 : ℂ) else ψ (c1 * (-1 - a / c0))) =
      if c0 = -a then (Fintype.card F : ℂ) else 0 := by
    intro c0
    by_cases h0 : c0 = 0
    · have : c0 ≠ -a := by rw [h0]; exact fun e => ha (neg_eq_zero.mp e.symm)
      simp [h0, ha]
    · simp only [h0, if_false]
      rw [AddChar.sum_mulShift _ hψ]
      have hiff : (-1 - a / c0 = 0) ↔ c0 = -a := by
        constructor
        · intro e; field_simp at e; linear_combination -e
        · intro e; subst e; field_simp; ring
      simp only [hiff]
      split_ifs <;> simp
  simp_rw [hin]
  simp

theorem degSum_ge_three (hψ : ψ ≠ 1) {m : ℕ} (hm : 3 ≤ m) : degSum ψ a m = 0 := by
  obtain ⟨s, hs⟩ : ∃ s : F, ψ (-s) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hψ
    ext x
    simpa using hcon (-x)
  set j : Fin m := ⟨m - 1, by omega⟩
  have hj0 : (0 : ℕ) ≠ (j : ℕ) := by simp [j]; omega
  have hj1 : (1 : ℕ) ≠ (j : ℕ) := by simp [j]; omega
  rw [degSum, sum_monicDeg]
  set W : (Fin m → F) → ℂ := fun c => klW ψ a (monicOf m c)
  have hshift : ∀ c, W (c + Pi.single j s) = ψ (-s) * W c := by
    intro c
    have hc0 : (c + Pi.single j s : Fin m → F) ⟨0, by omega⟩ = c ⟨0, by omega⟩ := by
      simp [Fin.ext_iff, hj0]
    have hc1 : (c + Pi.single j s : Fin m → F) ⟨1, by omega⟩ = c ⟨1, by omega⟩ := by
      simp [Fin.ext_iff, hj1]
    have hcj : (c + Pi.single j s : Fin m → F) j = c j + s := by simp
    simp only [W, klW, monicOf_nextCoeff (by omega : 1 ≤ m), monicOf_coeff]
    simp only [dif_pos (by omega : 0 < m), dif_pos (by omega : 1 < m)]
    rw [hc0, hc1]
    change _ = ψ (-s) * (if c ⟨0, _⟩ = 0 then 0 else ψ (-c j - _))
    rw [hcj]
    split_ifs
    · simp
    · rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have htot : (∑ c, W c) = ψ (-s) * ∑ c, W c := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight (Pi.single j s : Fin m → F)) _ _ (fun c => ?_)
    have := hshift (c - Pi.single j s)
    rw [sub_add_cancel] at this
    simpa using this
  have : (1 - ψ (-s)) * ∑ c, W c = 0 := by rw [sub_mul, one_mul, ← htot, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hs))

end weight

end GaloisForLFunctions.RHTower.WeilKloosterman
