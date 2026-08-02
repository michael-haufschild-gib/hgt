import GaloisForLFunctions.HTGeometry.GammaOrbitRationalIncrement

/-!
# The rational increment matrix of a family of shifted digammas

The unit shift sends `ψ(s+λ)` to `ψ(s+λ) + 1/(s+λ)`, so the jet of order `j` picks up the rational
increment `(-1)^j j!/(s+λ)^{j+1}`.  A differential relation among finitely many shifted digammas
produces a constant matrix `δ` of charges — one per translate and jet order — with

```text
w(X+1) − w(X) = ∑_{i,j} δ_{i,j} (-1)^j j!/(X+λ_i)^{j+1}
```

for a rational `w`.  Over a common denominator the right side is a rational function whose numerator
at `-λ_i` is the top charge of that translate times a nonzero product of shift differences, while
pairwise incongruence keeps the denominator from vanishing anywhere else on the orbit of `-λ_i`.  A
shift coboundary cannot have exactly one pole on an orbit, so the top layer vanishes; descending on
the jet order kills the whole matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

open Polynomial

variable {r : ℕ}

/-- The rational increment of the jet of order `j` of `ψ(s+λ_i)`. -/
def familyIncrement (lam : Fin r → ℂ) (i : Fin r) (j : ℕ) : RatFunc ℂ :=
  RatFunc.C ((-1 : ℂ) ^ j * (j.factorial : ℂ)) / (RatFunc.X + RatFunc.C (lam i)) ^ (j + 1)

/-- The numerator of a charge matrix over the common denominator of the family. -/
def familyNumerator (lam : Fin r → ℂ) (N : ℕ) (delta : Fin r → Fin (N + 1) → ℂ) :
    Polynomial ℂ :=
  ∑ i : Fin r, ∑ j : Fin (N + 1),
    Polynomial.C (delta i j * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ))) *
      gammaOrbitFactor lam i ^ (N - (j : ℕ)) *
        ∏ i' ∈ Finset.univ.erase i, gammaOrbitFactor lam i' ^ (N + 1)

/-- A charge matrix combination of the increments, over the common denominator. -/
theorem familyIncrement_commonDenominator (lam : Fin r → ℂ) (N : ℕ)
    (delta : Fin r → Fin (N + 1) → ℂ) :
    ∑ i : Fin r, ∑ j : Fin (N + 1),
        algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement lam i (j : ℕ) =
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (familyNumerator lam N delta) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (gammaOrbitCommonDenominator lam N) := by
  classical
  rw [familyNumerator, gammaOrbitCommonDenominator, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [familyIncrement, map_mul, map_mul, map_pow, map_prod]
  simp only [map_mul, map_pow, map_prod, gammaOrbitFactor, map_add,
    RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hfac : RatFunc.X + RatFunc.C (lam i) ≠ 0 := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (lam i))
  have hsplit :
      (∏ x : Fin r, (RatFunc.X + RatFunc.C (lam x)) ^ (N + 1)) =
        (RatFunc.X + RatFunc.C (lam i)) ^ (N + 1) *
          ∏ x ∈ Finset.univ.erase i,
            (RatFunc.X + RatFunc.C (lam x)) ^ (N + 1) :=
    (Finset.mul_prod_erase Finset.univ
      (fun x : Fin r => (RatFunc.X + RatFunc.C (lam x)) ^ (N + 1))
      (Finset.mem_univ i)).symm
  have hrest :
      (∏ x ∈ Finset.univ.erase i,
        (RatFunc.X + RatFunc.C (lam x)) ^ (N + 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro x _
    apply pow_ne_zero
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (lam x))
  rw [hsplit]
  have hj : (j : ℕ) + 1 + (N - (j : ℕ)) = N + 1 := by omega
  rw [show (RatFunc.X + RatFunc.C (lam i)) ^ (N + 1) =
      (RatFunc.X + RatFunc.C (lam i)) ^ ((j : ℕ) + 1) *
        (RatFunc.X + RatFunc.C (lam i)) ^ (N - (j : ℕ)) by rw [← pow_add, hj]]
  field_simp [hfac, hrest]
  simp [RatFunc.algebraMap_eq_C, mul_comm]

/-- At the pole of one translate only its top charge survives, multiplied by a nonzero product of
shift differences. -/
theorem familyNumerator_eval_center_ne_zero (lam : Fin r → ℂ)
    (i₀ : Fin r) (hsep : ∀ i, i ≠ i₀ → ∀ n : ℤ, lam i - lam i₀ ≠ (n : ℂ))
    (N : ℕ) (delta : Fin r → Fin (N + 1) → ℂ)
    (hdelta : delta i₀ ⟨N, Nat.lt_succ_self N⟩ ≠ 0) :
    (familyNumerator lam N delta).eval (-lam i₀) ≠ 0 := by
  classical
  rw [familyNumerator]
  change (Polynomial.evalRingHom (-lam i₀))
      (∑ i : Fin r, ∑ j : Fin (N + 1),
        Polynomial.C (delta i j * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ))) *
          gammaOrbitFactor lam i ^ (N - (j : ℕ)) *
            ∏ i' ∈ Finset.univ.erase i, gammaOrbitFactor lam i' ^ (N + 1)) ≠ 0
  rw [map_sum]
  have hprodZero : ∀ i : Fin r, i ≠ i₀ →
      (∏ i' ∈ Finset.univ.erase i, (-lam i₀ + lam i') ^ (N + 1)) = 0 := by
    intro i hii
    rw [Finset.prod_eq_zero_iff]
    refine ⟨i₀, by simp [Ne.symm hii], ?_⟩
    rw [show -lam i₀ + lam i₀ = 0 by ring, zero_pow (by omega : N + 1 ≠ 0)]
  have hrow : ∀ i : Fin r,
      (Polynomial.evalRingHom (-lam i₀))
        (∑ j : Fin (N + 1),
          Polynomial.C (delta i j * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ))) *
            gammaOrbitFactor lam i ^ (N - (j : ℕ)) *
              ∏ i' ∈ Finset.univ.erase i, gammaOrbitFactor lam i' ^ (N + 1)) =
        if i = i₀ then
          delta i₀ ⟨N, Nat.lt_succ_self N⟩ * ((-1 : ℂ) ^ N * (N.factorial : ℂ)) *
            ∏ i' ∈ Finset.univ.erase i₀, (lam i' - lam i₀) ^ (N + 1)
        else 0 := by
    intro i
    rw [map_sum]
    change (∑ j : Fin (N + 1),
        (Polynomial.C (delta i j * ((-1 : ℂ) ^ (j : ℕ) * ((j : ℕ).factorial : ℂ))) *
          gammaOrbitFactor lam i ^ (N - (j : ℕ)) *
            ∏ i' ∈ Finset.univ.erase i, gammaOrbitFactor lam i' ^ (N + 1)).eval
          (-lam i₀)) = _
    by_cases hii : i = i₀
    · subst i
      rw [if_pos rfl]
      rw [Finset.sum_eq_single ⟨N, Nat.lt_succ_self N⟩]
      · simp [Polynomial.eval_prod, gammaOrbitFactor, sub_eq_add_neg, add_comm]
      · intro j _ hj
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_prod, gammaOrbitFactor, Polynomial.eval_add, Polynomial.eval_X]
        have hjN : (j : ℕ) ≠ N := fun hval => hj (Fin.ext hval)
        have hpos : 0 < N - (j : ℕ) := by omega
        rw [show -lam i₀ + lam i₀ = 0 by ring, zero_pow hpos.ne']
        simp
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    · rw [if_neg hii]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_prod, gammaOrbitFactor, Polynomial.eval_add, Polynomial.eval_X]
      rw [hprodZero i hii, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  rw [Finset.sum_eq_single i₀]
  · simp only [if_true]
    apply mul_ne_zero
    · exact mul_ne_zero hdelta
        (mul_ne_zero (pow_ne_zero _ (by norm_num))
          (by exact_mod_cast Nat.factorial_ne_zero N))
    · rw [Finset.prod_ne_zero_iff]
      intro i hi
      have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
      exact pow_ne_zero _ (by simpa using hsep i hii 0)
  · intro i _ hi
    rw [if_neg hi]
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- **The top jet layer of a shift-summable charge matrix vanishes.** -/
theorem familyIncrement_top_eq_zero (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {N : ℕ} {w : RatFunc ℂ} {delta : Fin r → Fin (N + 1) → ℂ}
    (h : ratShift w - w = ∑ i : Fin r, ∑ j : Fin (N + 1),
      algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement lam i (j : ℕ))
    (i₀ : Fin r) : delta i₀ ⟨N, Nat.lt_succ_self N⟩ = 0 := by
  classical
  by_contra hd
  have hsep : ∀ i, i ≠ i₀ → ∀ n : ℤ, lam i - lam i₀ ≠ (n : ℂ) := fun i hi => hincong i i₀ hi
  refine ratShift_sub_ne_of_single_orbit_pole (-lam i₀)
    (gammaOrbitCommonDenominator_ne_zero lam N)
    (familyNumerator_eval_center_ne_zero lam i₀ hsep N delta hd)
    (fun n => by
      simpa [add_comm] using gammaOrbitCommonDenominator_orbit_zero_iff lam i₀ hsep N n)
    w ?_
  rw [h, familyIncrement_commonDenominator]

/-- **Equation (8) for a family.**  With pairwise incongruent shifts, no nonzero constant charge
matrix on the jets of the shifted simple poles is a rational shift coboundary. -/
theorem ratShift_sub_familyIncrement_combination (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    {N : ℕ} {w : RatFunc ℂ} {delta : Fin r → Fin (N + 1) → ℂ}
    (h : ratShift w - w = ∑ i : Fin r, ∑ j : Fin (N + 1),
      algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement lam i (j : ℕ)) :
    ∀ i j, delta i j = 0 := by
  classical
  induction N with
  | zero =>
      intro i j
      have hj : j = ⟨0, Nat.lt_succ_self 0⟩ := Fin.ext (by omega)
      rw [hj]
      exact familyIncrement_top_eq_zero lam hincong h i
  | succ N ih =>
      have htop : ∀ i, delta i ⟨N + 1, Nat.lt_succ_self (N + 1)⟩ = 0 := fun i =>
        familyIncrement_top_eq_zero lam hincong h i
      have hlast : ∀ i, delta i (Fin.last (N + 1)) = 0 := fun i => htop i
      set delta' : Fin r → Fin (N + 1) → ℂ := fun i j => delta i j.castSucc with hdelta'
      have hlower : ratShift w - w = ∑ i : Fin r, ∑ j : Fin (N + 1),
          algebraMap ℂ (RatFunc ℂ) (delta' i j) * familyIncrement lam i (j : ℕ) := by
        rw [h]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.sum_univ_castSucc]
        simp [delta', hlast i]
      have hz := ih (delta := delta') hlower
      intro i j
      by_cases hj : (j : ℕ) = N + 1
      · have hjeq : j = Fin.last (N + 1) := Fin.ext (by simpa using hj)
        rw [hjeq]
        exact hlast i
      · have hjlt : (j : ℕ) < N + 1 := by omega
        have := hz i ⟨j, hjlt⟩
        simpa [delta'] using this

end

end GaloisForLFunctions.HTGeometry
