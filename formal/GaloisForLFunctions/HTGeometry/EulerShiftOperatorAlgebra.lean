import GaloisForLFunctions.HTGeometry.ShiftPolynomialBounds

/-!
# Euler-form operators presented by their shift polynomials

A linear differential operator in the Euler basis is determined by the family of polynomials

```text
L = ∑_{μ ≥ 0} t^μ Φ_μ(θ) ,      θ = t d/dt ,
```

and acts on coefficients by the single convolution `coeff_n (L F) = ∑_{k ≤ n} Φ_{n-k}(k) f_k`.  The
presentation by the family `Φ` rather than by coefficients `B_j` of powers of `θ` is what makes the
ring structure visible: since `θ ∘ t^b = t^b ∘ (θ + b)`,

```text
(t^a Ψ(θ)) ∘ (t^b Φ(θ)) = t^{a+b} Ψ(θ + b) Φ(θ) ,
```

so composition is the convolution

```text
(Ψ ⋆ Φ)_ν = ∑_{a + b = ν} Ψ_a(X + b) · Φ_b(X) .
```

Nothing here is analytic: the identities hold for arbitrary families of polynomials, and the
convolution is a genuine associative product because it computes composition of the induced maps.
-/

open PowerSeries
open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-! ### The action -/

/-- The operator determined by a family of shift polynomials. -/
noncomputable def shiftOp (Φ : ℕ → Polynomial ℂ) (F : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1),
    (Φ (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F

@[simp] theorem coeff_shiftOp (Φ : ℕ → Polynomial ℂ) (F : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (shiftOp Φ F)
      = ∑ k ∈ Finset.range (n + 1),
          (Φ (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k F :=
  PowerSeries.coeff_mk _ _

/-- An operator written with coefficients of powers of `θ` is the operator of its shift
polynomials. -/
theorem shiftOp_shiftPolynomial {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ) (F : PowerSeries ℂ) :
    shiftOp (shiftPolynomial B) F = eulerLinearOp B F := by
  ext n
  rw [coeff_shiftOp, coeff_eulerLinearOp_range]

theorem shiftOp_add (Φ : ℕ → Polynomial ℂ) (F G : PowerSeries ℂ) :
    shiftOp Φ (F + G) = shiftOp Φ F + shiftOp Φ G := by
  ext n
  rw [coeff_shiftOp, map_add, coeff_shiftOp, coeff_shiftOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add]
  ring

theorem shiftOp_zero_family (F : PowerSeries ℂ) : shiftOp (fun _ => 0) F = 0 := by
  ext n
  simp

/-! ### Composition -/

/-- The convolution of two families of shift polynomials, which computes the composition of the
operators they determine. -/
noncomputable def shiftComp (Ψ Φ : ℕ → Polynomial ℂ) : ℕ → Polynomial ℂ := fun ν =>
  ∑ b ∈ Finset.range (ν + 1),
    (Ψ (ν - b)).comp (Polynomial.X + Polynomial.C ((b : ℕ) : ℂ)) * Φ b

/-- **The convolution of shift polynomials is composition of operators.** -/
theorem shiftOp_shiftComp (Ψ Φ : ℕ → Polynomial ℂ) (F : PowerSeries ℂ) :
    shiftOp (shiftComp Ψ Φ) F = shiftOp Ψ (shiftOp Φ F) := by
  classical
  ext n
  rw [coeff_shiftOp, coeff_shiftOp]
  have hR : ∑ k ∈ Finset.range (n + 1),
        (Ψ (n - k)).eval ((k : ℕ) : ℂ) * PowerSeries.coeff k (shiftOp Φ F)
      = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (k + 1),
          (Ψ (n - k)).eval ((k : ℕ) : ℂ) * ((Φ (k - j)).eval ((j : ℕ) : ℂ)
            * PowerSeries.coeff j F) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_shiftOp, Finset.mul_sum]
  rw [hR, Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Icc j n)
    (by intro x y; simp only [Finset.mem_range, Finset.mem_Icc]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [shiftComp, Polynomial.eval_finsetSum, Finset.sum_mul]
  have hIcc : Finset.Icc j n = Finset.Ico j (n + 1) := by
    ext x
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hidx : n + 1 - j = (n - j) + 1 := by omega
  rw [hidx]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbn : b ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have h1 : n - (j + b) = n - j - b := by omega
  have h2 : (j + b) - j = b := by omega
  rw [h1, h2, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  push_cast
  ring

/-- The degree of a convolution is at most the sum of the degrees. -/
theorem natDegree_shiftComp_le {Ψ Φ : ℕ → Polynomial ℂ} {m₁ m₂ : ℕ}
    (hΨ : ∀ a, (Ψ a).natDegree ≤ m₁) (hΦ : ∀ b, (Φ b).natDegree ≤ m₂) (ν : ℕ) :
    (shiftComp Ψ Φ ν).natDegree ≤ m₁ + m₂ := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  refine le_trans Polynomial.natDegree_mul_le ?_
  refine Nat.add_le_add ?_ (hΦ b)
  refine le_trans (Polynomial.natDegree_comp_le) ?_
  have hX : (Polynomial.X + Polynomial.C ((b : ℕ) : ℂ)).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    simp
  calc (Ψ (ν - b)).natDegree * (Polynomial.X + Polynomial.C ((b : ℕ) : ℂ)).natDegree
      ≤ (Ψ (ν - b)).natDegree * 1 := Nat.mul_le_mul_left _ hX
    _ = (Ψ (ν - b)).natDegree := by ring
    _ ≤ m₁ := hΨ (ν - b)

/-! ### Boundedness of a family, and its stability under composition -/

/-- A family of shift polynomials is *bounded of order `m`* when its values along the natural
numbers are geometric in the shift and of polynomial size `m` in the argument.  This is exactly the
estimate a convergent operator supplies. -/
def IsBoundedShiftFamily (m : ℕ) (Φ : ℕ → Polynomial ℂ) : Prop :=
  ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ μ k : ℕ,
    ‖(Φ μ).eval ((k : ℕ) : ℂ)‖ ≤ C * ρ ^ μ * (((k : ℝ)) + 1) ^ m

theorem isBoundedShiftFamily_shiftPolynomial {m : ℕ} (B : Fin (m + 1) → PowerSeries ℂ)
    (hB : ∀ j, IsGevreySeries 0 (B j)) : IsBoundedShiftFamily m (shiftPolynomial B) := by
  obtain ⟨C, ρ, hC, hρ, h⟩ := exists_bound_shiftPolynomial B hB
  exact ⟨C, ρ, hC, hρ, h⟩

/-- **Boundedness is stable under composition**, with the orders adding. -/
theorem isBoundedShiftFamily_shiftComp {m₁ m₂ : ℕ} {Ψ Φ : ℕ → Polynomial ℂ}
    (hΨ : IsBoundedShiftFamily m₁ Ψ) (hΦ : IsBoundedShiftFamily m₂ Φ) :
    IsBoundedShiftFamily (m₁ + m₂) (shiftComp Ψ Φ) := by
  classical
  obtain ⟨C₁, ρ₁, hC₁, hρ₁, h₁⟩ := hΨ
  obtain ⟨C₂, ρ₂, hC₂, hρ₂, h₂⟩ := hΦ
  obtain ⟨Cm, hCm1, hCm⟩ := exists_succ_pow_le_const_mul_pow m₁ (by norm_num : (1 : ℝ) < 2)
  obtain ⟨C0, hC01, hC0⟩ := exists_succ_pow_le_const_mul_pow 1 (by norm_num : (1 : ℝ) < 2)
  set ρ₀ : ℝ := max ρ₁ ρ₂ with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_of_lt_of_le hρ₁ (le_max_left _ _)
  refine ⟨C₁ * C₂ * Cm * C0, 4 * ρ₀, by positivity, by positivity, fun ν k => ?_⟩
  have hterm : ∀ b ∈ Finset.range (ν + 1),
      ‖((Ψ (ν - b)).comp (Polynomial.X + Polynomial.C ((b : ℕ) : ℂ)) * Φ b).eval ((k : ℕ) : ℂ)‖
        ≤ (C₁ * C₂ * Cm) * (2 * ρ₀) ^ ν * (((k : ℝ)) + 1) ^ (m₁ + m₂) := by
    intro b hb
    have hbν : b ≤ ν := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hcast : ((k : ℕ) : ℂ) + ((b : ℕ) : ℂ) = (((k + b : ℕ)) : ℂ) := by push_cast; ring
    rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, hcast, norm_mul]
    have hA := h₁ (ν - b) (k + b)
    have hB := h₂ b k
    have hsplit : (((k + b : ℕ) : ℝ)) + 1 ≤ (((k : ℝ)) + 1) * (((b : ℝ)) + 1) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) b]
    have hpow : ((((k + b : ℕ) : ℝ)) + 1) ^ m₁
        ≤ (((k : ℝ)) + 1) ^ m₁ * (((b : ℝ)) + 1) ^ m₁ := by
      calc ((((k + b : ℕ) : ℝ)) + 1) ^ m₁
          ≤ ((((k : ℝ)) + 1) * (((b : ℝ)) + 1)) ^ m₁ :=
            pow_le_pow_left₀ (by positivity) hsplit m₁
        _ = (((k : ℝ)) + 1) ^ m₁ * (((b : ℝ)) + 1) ^ m₁ := by rw [mul_pow]
    have hA' : ‖(Ψ (ν - b)).eval (((k + b : ℕ)) : ℂ)‖
        ≤ C₁ * ρ₁ ^ (ν - b) * ((((k : ℝ)) + 1) ^ m₁ * (((b : ℝ)) + 1) ^ m₁) := by
      refine le_trans hA ?_
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hprod : ‖(Ψ (ν - b)).eval (((k + b : ℕ)) : ℂ)‖ * ‖(Φ b).eval ((k : ℕ) : ℂ)‖
        ≤ (C₁ * ρ₁ ^ (ν - b) * ((((k : ℝ)) + 1) ^ m₁ * (((b : ℝ)) + 1) ^ m₁))
          * (C₂ * ρ₂ ^ b * (((k : ℝ)) + 1) ^ m₂) :=
      mul_le_mul hA' hB (norm_nonneg _) (by positivity)
    refine le_trans hprod ?_
    have hρa : ρ₁ ^ (ν - b) ≤ ρ₀ ^ (ν - b) := pow_le_pow_left₀ (le_of_lt hρ₁) (le_max_left _ _) _
    have hρb : ρ₂ ^ b ≤ ρ₀ ^ b := pow_le_pow_left₀ (le_of_lt hρ₂) (le_max_right _ _) _
    have hρsum : ρ₀ ^ (ν - b) * ρ₀ ^ b = ρ₀ ^ ν := by
      rw [← pow_add]
      congr 1
      omega
    have hbpow : (((b : ℝ)) + 1) ^ m₁ ≤ Cm * 2 ^ b := hCm b
    have h2b : (2 : ℝ) ^ b ≤ 2 ^ ν := pow_le_pow_right₀ (by norm_num) hbν
    calc (C₁ * ρ₁ ^ (ν - b) * ((((k : ℝ)) + 1) ^ m₁ * (((b : ℝ)) + 1) ^ m₁))
          * (C₂ * ρ₂ ^ b * (((k : ℝ)) + 1) ^ m₂)
        = (C₁ * C₂) * (ρ₁ ^ (ν - b) * ρ₂ ^ b) * (((b : ℝ)) + 1) ^ m₁
            * ((((k : ℝ)) + 1) ^ m₁ * (((k : ℝ)) + 1) ^ m₂) := by ring
      _ ≤ (C₁ * C₂) * (ρ₀ ^ (ν - b) * ρ₀ ^ b) * (Cm * 2 ^ ν)
            * ((((k : ℝ)) + 1) ^ m₁ * (((k : ℝ)) + 1) ^ m₂) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul ?_ ?_ (by positivity) (by positivity))
            (by positivity)
          · exact mul_le_mul_of_nonneg_left (mul_le_mul hρa hρb (by positivity) (by positivity))
              (by positivity)
          · exact le_trans hbpow (mul_le_mul_of_nonneg_left h2b (by linarith))
      _ = (C₁ * C₂ * Cm) * (ρ₀ ^ ν * 2 ^ ν) * (((k : ℝ)) + 1) ^ (m₁ + m₂) := by
          rw [hρsum, pow_add]
          ring
      _ = (C₁ * C₂ * Cm) * (2 * ρ₀) ^ ν * (((k : ℝ)) + 1) ^ (m₁ + m₂) := by
          rw [mul_pow]
          ring
  have hsum : ‖(shiftComp Ψ Φ ν).eval ((k : ℕ) : ℂ)‖
      ≤ ((ν : ℝ) + 1) * ((C₁ * C₂ * Cm) * (2 * ρ₀) ^ ν * (((k : ℝ)) + 1) ^ (m₁ + m₂)) := by
    rw [shiftComp, Polynomial.eval_finsetSum]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (((ν + 1 : ℕ)) : ℝ) = (ν : ℝ) + 1 := by push_cast; ring
    rw [this]
  refine le_trans hsum ?_
  have hν : ((ν : ℝ) + 1) ≤ C0 * 2 ^ ν := by
    have h := hC0 ν
    rwa [pow_one] at h
  calc ((ν : ℝ) + 1) * ((C₁ * C₂ * Cm) * (2 * ρ₀) ^ ν * (((k : ℝ)) + 1) ^ (m₁ + m₂))
      ≤ (C0 * 2 ^ ν) * ((C₁ * C₂ * Cm) * (2 * ρ₀) ^ ν * (((k : ℝ)) + 1) ^ (m₁ + m₂)) := by
        refine mul_le_mul_of_nonneg_right hν (by positivity)
    _ = (C₁ * C₂ * Cm * C0) * (2 ^ ν * (2 * ρ₀) ^ ν) * (((k : ℝ)) + 1) ^ (m₁ + m₂) := by ring
    _ = (C₁ * C₂ * Cm * C0) * (4 * ρ₀) ^ ν * (((k : ℝ)) + 1) ^ (m₁ + m₂) := by
        rw [← mul_pow]
        ring_nf

end GaloisForLFunctions.HTGeometry
