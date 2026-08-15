import GaloisForLFunctions.HTGeometry.HighDegreeJetFreedom

/-!
# The Euler operator is triangular on jets

The Euler operator `Θ p = X · p'` satisfies

```text
Θ^r p = ∑_{k ≤ r} S(r, k) · X^k · p^(k),      S(r+1, k) = k · S(r, k) + S(r, k-1),
```

with `S(r, r) = 1`.  At a nonzero point the transform from the derivative jets to the Euler jets is
therefore triangular with unit-power diagonal, hence invertible.  Combined with the freedom of the
derivative jets in a high-degree window, the *Euler* jets at finitely many distinct nonzero nodes are
freely prescribable by coefficients of arbitrarily high degree.

The Euler jets are the ones a pencil carrier produces: `δ = D_w` acts on `Ψ ∘ exp ∘ L` by
`(L w)^r · Θ^r Ψ ∘ exp ∘ L`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Euler operator on polynomials. -/
def polyEuler (p : Polynomial ℂ) : Polynomial ℂ := X * Polynomial.derivative p

/-- The coefficients of the Euler operator in the derivative jets: Stirling numbers of the second
kind. -/
def eulerStirling : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | r + 1, k + 1 => ((k + 1 : ℕ) : ℂ) * eulerStirling r (k + 1) + eulerStirling r k

@[simp] theorem eulerStirling_zero_zero : eulerStirling 0 0 = 1 := rfl

@[simp] theorem eulerStirling_zero_succ (k : ℕ) : eulerStirling 0 (k + 1) = 0 := rfl

@[simp] theorem eulerStirling_succ_zero (r : ℕ) : eulerStirling (r + 1) 0 = 0 := rfl

theorem eulerStirling_succ_succ (r k : ℕ) :
    eulerStirling (r + 1) (k + 1) =
      ((k + 1 : ℕ) : ℂ) * eulerStirling r (k + 1) + eulerStirling r k := rfl

theorem eulerStirling_of_lt : ∀ r k : ℕ, r < k → eulerStirling r k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | r + 1, k + 1, h => by
      rw [eulerStirling_succ_succ, eulerStirling_of_lt r (k + 1) (by omega),
        eulerStirling_of_lt r k (by omega), mul_zero, add_zero]

theorem eulerStirling_self : ∀ r : ℕ, eulerStirling r r = 1
  | 0 => rfl
  | r + 1 => by
      rw [eulerStirling_succ_succ, eulerStirling_of_lt r (r + 1) (Nat.lt_succ_self r),
        eulerStirling_self r, mul_zero, zero_add]

/-- One step of the Euler operator on a jet term. -/
theorem polyEuler_jet_term (s : ℂ) (k : ℕ) (p : Polynomial ℂ) :
    X * Polynomial.derivative
        (Polynomial.C s * X ^ k * Polynomial.derivative^[k] p) =
      Polynomial.C (((k : ℕ) : ℂ) * s) * X ^ k * Polynomial.derivative^[k] p +
        Polynomial.C s * X ^ (k + 1) * Polynomial.derivative^[k + 1] p := by
  rw [mul_assoc, Polynomial.derivative_C_mul, Polynomial.derivative_mul,
    Polynomial.derivative_X_pow, ← Function.iterate_succ_apply' Polynomial.derivative k]
  cases k with
  | zero =>
      simp
      ring
  | succ k =>
      rw [show (k + 1 - 1) = k by omega, map_mul]
      ring

/-- **The Euler operator is triangular in the derivative jets.** -/
theorem polyEuler_iterate_eq (r : ℕ) (p : Polynomial ℂ) :
    polyEuler^[r] p =
      ∑ k ∈ Finset.range (r + 1),
        Polynomial.C (eulerStirling r k) * X ^ k * Polynomial.derivative^[k] p := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih, polyEuler, Polynomial.derivative_sum, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun k _ => polyEuler_jet_term (eulerStirling r k) k p,
        Finset.sum_add_distrib]
      have hA : (∑ k ∈ Finset.range (r + 1),
            Polynomial.C (((k : ℕ) : ℂ) * eulerStirling r k) * X ^ k *
              Polynomial.derivative^[k] p) =
          ∑ k ∈ Finset.range (r + 1),
            Polynomial.C (((k + 1 : ℕ) : ℂ) * eulerStirling r (k + 1)) * X ^ (k + 1) *
              Polynomial.derivative^[k + 1] p := by
        rw [Finset.sum_range_succ' (fun k =>
          Polynomial.C (((k : ℕ) : ℂ) * eulerStirling r k) * X ^ k *
            Polynomial.derivative^[k] p) r]
        rw [Finset.sum_range_succ (fun k =>
          Polynomial.C (((k + 1 : ℕ) : ℂ) * eulerStirling r (k + 1)) * X ^ (k + 1) *
            Polynomial.derivative^[k + 1] p) r]
        rw [eulerStirling_of_lt r (r + 1) (Nat.lt_succ_self r)]
        simp
      have hRHS : (∑ k ∈ Finset.range (r + 1 + 1),
            Polynomial.C (eulerStirling (r + 1) k) * X ^ k * Polynomial.derivative^[k] p) =
          ∑ k ∈ Finset.range (r + 1),
            Polynomial.C (eulerStirling (r + 1) (k + 1)) * X ^ (k + 1) *
              Polynomial.derivative^[k + 1] p := by
        rw [Finset.sum_range_succ' (fun k =>
          Polynomial.C (eulerStirling (r + 1) k) * X ^ k * Polynomial.derivative^[k] p) (r + 1)]
        simp
      rw [hA, hRHS, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [eulerStirling_succ_succ, map_add]
      ring

/-- The evaluated triangular identity. -/
theorem eval_polyEuler_iterate (r : ℕ) (p : Polynomial ℂ) (x : ℂ) :
    (polyEuler^[r] p).eval x =
      ∑ k ∈ Finset.range (r + 1),
        eulerStirling r k * x ^ k * (Polynomial.derivative^[k] p).eval x := by
  rw [polyEuler_iterate_eq, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- The evaluated triangular identity, with the sum taken over a full jet range. -/
theorem eval_polyEuler_iterate_range {r m : ℕ} (hr : r < m) (p : Polynomial ℂ) (x : ℂ) :
    (polyEuler^[r] p).eval x =
      ∑ k ∈ Finset.range m,
        eulerStirling r k * x ^ k * (Polynomial.derivative^[k] p).eval x := by
  rw [eval_polyEuler_iterate]
  have hsub : Finset.range (r + 1) ⊆ Finset.range m := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  refine Finset.sum_subset hsub fun k _ hk => ?_
  have hkr : r < k := by
    rw [Finset.mem_range] at hk
    omega
  rw [eulerStirling_of_lt r k hkr, zero_mul, zero_mul]

/-! ### The triangular transform between derivative jets and Euler jets -/

/-- The transform sending a derivative-jet vector at the nodes to the corresponding Euler-jet
vector. -/
def eulerTransform {K : ℕ} (x : Fin K → ℂ) (m : ℕ) :
    (Fin K × Fin m → ℂ) →ₗ[ℂ] (Fin K × Fin m → ℂ) :=
  LinearMap.pi fun p => ∑ k : Fin m,
    (eulerStirling (p.2 : ℕ) (k : ℕ) * (x p.1) ^ (k : ℕ)) • LinearMap.proj (R := ℂ) (p.1, k)

theorem eulerTransform_apply {K : ℕ} (x : Fin K → ℂ) (m : ℕ) (v : Fin K × Fin m → ℂ)
    (p : Fin K × Fin m) :
    eulerTransform x m v p =
      ∑ k : Fin m, eulerStirling (p.2 : ℕ) (k : ℕ) * (x p.1) ^ (k : ℕ) * v (p.1, k) := by
  rw [eulerTransform, LinearMap.pi_apply, LinearMap.coe_sum, Finset.sum_apply]
  rfl

/-- **The triangular transform is injective at nonzero nodes.** -/
theorem eulerTransform_injective {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ) :
    Function.Injective (eulerTransform x m) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  have hkey : ∀ r : ℕ, ∀ hr : r < m, ∀ a : Fin K, v (a, ⟨r, hr⟩) = 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
        intro hr a
        have hzero := congrFun hv (a, (⟨r, hr⟩ : Fin m))
        rw [eulerTransform_apply] at hzero
        have hsingle : ∑ k : Fin m,
            eulerStirling r (k : ℕ) * (x a) ^ (k : ℕ) * v (a, k) =
              eulerStirling r r * (x a) ^ r * v (a, ⟨r, hr⟩) := by
          refine Finset.sum_eq_single (⟨r, hr⟩ : Fin m) ?_ ?_
          · intro k _ hk
            rcases lt_trichotomy (k : ℕ) r with hlt | heq | hgt
            · rw [ih (k : ℕ) hlt k.2 a]
              ring
            · exact absurd (Fin.ext heq) hk
            · rw [eulerStirling_of_lt r (k : ℕ) hgt]
              ring
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [hsingle, eulerStirling_self, one_mul] at hzero
        exact (mul_eq_zero.mp (by simpa using hzero)).resolve_left (pow_ne_zero _ (hx0 a))
  funext p
  have hp := hkey (p.2 : ℕ) p.2.isLt p.1
  simpa using hp

/-- **The triangular transform is onto at nonzero nodes.** -/
theorem eulerTransform_surjective {K : ℕ} {x : Fin K → ℂ} (hx0 : ∀ a, x a ≠ 0) (m : ℕ) :
    Function.Surjective (eulerTransform x m) :=
  LinearMap.injective_iff_surjective.mp (eulerTransform_injective hx0 m)

/-! ### Free Euler jets -/

/-- **Free Euler jets from a high-degree window.**  For every Euler-jet target at `K` distinct
nonzero nodes and every starting degree `N`, some coefficient vector supported in `[N, N + K·m)`
realizes it. -/
theorem exists_windowLin_eulerJets {K : ℕ} {x : Fin K → ℂ} (hxinj : Function.Injective x)
    (hx0 : ∀ a, x a ≠ 0) (m N : ℕ) (J : Fin K × Fin m → ℂ) :
    ∃ c : Fin (K * m) → ℂ, ∀ (a : Fin K) (r : Fin m),
      (polyEuler^[(r : ℕ)] (windowLin N (K * m) c)).eval (x a) = J (a, r) := by
  obtain ⟨v, hv⟩ := eulerTransform_surjective hx0 m J
  obtain ⟨c, hc⟩ := exists_windowLin_jets hxinj hx0 m N v
  refine ⟨c, fun a r => ?_⟩
  rw [eval_polyEuler_iterate_range r.2, ← hv, eulerTransform_apply]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => eulerStirling (r : ℕ) k * (x a) ^ k *
      (Polynomial.derivative^[k] (windowLin N (K * m) c)).eval (x a)) m]
  exact Finset.sum_congr rfl fun k _ => by rw [hc a k]

end

end GaloisForLFunctions.HTGeometry
