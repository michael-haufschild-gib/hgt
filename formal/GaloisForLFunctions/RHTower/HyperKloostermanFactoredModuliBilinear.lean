import GaloisForLFunctions.RHTower.HyperKloostermanFactoredModuliCompleteSums

/-!
# A bilinear bound for `Kl₃` over the moduli `p s²`

For odd primes `p ∈ 𝒫`, primes `s ∈ 𝒮` distinct from them, and multipliers coprime to the moduli,
put `T = Σ_{s∈𝒮} Σ_{m≤L} α_m Σ_{p∈𝒫} K*(u m; p) K*(v m; s²)`. Here `K*` is `Kl₃` on unit
arguments. By twisted multiplicativity `Kl₃(am; ps²) = Kl₃(a s̄⁶ m; p) Kl₃(a p̄³ m; s²)`, so `T` is a
sum of `Kl₃` over the moduli `p s²` with arbitrary coefficients in `m`.

Cauchy–Schwarz over `(s, m)` with the `p`-sum kept inside, and completion of each off-diagonal pair
modulo `p₁p₂s²`, give (`norm_sq_factored_moduli_le`)

`|T|² ≤ |𝒮| ‖α‖² Σ_s (Σ_p 9s⁴(L/p + 1)(2p√p + 1)² + Σ_{p₁≠p₂} O(p₁, p₂, s))`,

`O = (L/(p₁p₂s²))·9s⁶ + A₁A₂(6s⁵(1 + log p₁p₂s²) + 9s⁵(1 + log p₁p₂s))`, `A_i = 2p_i√p_i + 1`.

With `|𝒫| ≍ P`, `|𝒮| ≍ S`, `Q = PS²` and `‖α‖² ≍ L`, compare with the trivial bound
`|𝒮||𝒫| L Q ≍ P²S³L`. The diagonal term saves `P^{1/2}` and the off-diagonal term saves
`(L/(PS))^{1/2}`, up to logarithms. This is the moduli saving that turns the forced zero of the
twisted symmetric-square family into `λ₁ ≥ 10/49`. At `Q = X^{4/7}`, `P = S² = √Q`, `L = Q^{5/4}` both
savings equal `Q^{1/4}`. The proof uses only Weil's bound for `Kl₂` and elementary stationary
phase modulo prime squares.
-/

open Finset

namespace GaloisForLFunctions.RHTower.HyperKloostermanFactoredModuli

open GaloisForLFunctions.RHTower.HyperKloostermanPrimeSquare
open GaloisForLFunctions.RHTower.RootOfUnityCompletion

noncomputable section

/-- `K*(am; n)` for natural data (zero when `n = 0`). -/
def klNat (n a m : ℕ) : ℂ :=
  if h : n = 0 then 0 else haveI : NeZero n := ⟨h⟩; klUnit n ((a : ZMod n) * (m : ZMod n))

theorem klNat_eq (n : ℕ) [NeZero n] (a m : ℕ) :
    klNat n a m = klUnit n ((a : ZMod n) * (m : ZMod n)) := by
  unfold klNat; rw [dif_neg (NeZero.ne n)]

/-- The off-diagonal bound, as a function of the two primes, the prime `s` and the length. -/
def offBound (p₁ p₂ s L : ℕ) : ℝ :=
  (L : ℝ) / (p₁ * p₂ * s ^ 2 : ℕ) * (9 * (s : ℝ) ^ 6) +
    (2 * p₁ * Real.sqrt p₁ + 1) * (2 * p₂ * Real.sqrt p₂ + 1) * (6 * (s : ℝ) ^ 5) *
      (1 + Real.log (p₁ * p₂ * s ^ 2 : ℕ)) +
    (2 * p₁ * Real.sqrt p₁ + 1) * (2 * p₂ * Real.sqrt p₂ + 1) * (9 * (s : ℝ) ^ 6) / s *
      (1 + Real.log (p₁ * p₂ * s : ℕ))

/-- The diagonal bound. -/
def diagBound (p s L : ℕ) : ℝ :=
  9 * (s : ℝ) ^ 4 * (((L : ℝ) / p + 1) * (2 * p * Real.sqrt p + 1) ^ 2)

theorem diag_le_nat {p s : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hs : s.Prime) {a b : ℕ}
    (ha : a.Coprime p) (hb : b.Coprime s) (L : ℕ) :
    ∑ m ∈ Finset.Icc 1 L, ‖klNat p a m * klNat (s ^ 2) b m‖ ^ 2 ≤ diagBound p s L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact s.Prime := ⟨hs⟩
  have hb2 : b.Coprime (s ^ 2) := Nat.Coprime.pow_right 2 hb
  have := diag_le (p := p) (s := s) hp2 (ZMod.unitOfCoprime a ha)
    (ZMod.unitOfCoprime b hb2) L
  simp only [ZMod.coe_unitOfCoprime] at this
  simp only [klNat_eq]
  exact this

theorem offdiag_le_nat {p₁ p₂ s : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hs : s.Prime)
    (hp₁2 : p₁ ≠ 2) (hp₂2 : p₂ ≠ 2) (h12 : p₁ ≠ p₂) (h1s : p₁ ≠ s) (h2s : p₂ ≠ s)
    {a₁ a₂ b₁ b₂ : ℕ} (ha₁ : a₁.Coprime p₁) (ha₂ : a₂.Coprime p₂) (hb₁ : b₁.Coprime s)
    (hb₂ : b₂.Coprime s) (L : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 L, (klNat p₁ a₁ m * klNat (s ^ 2) b₁ m) *
        star (klNat p₂ a₂ m * klNat (s ^ 2) b₂ m)‖ ≤ offBound p₁ p₂ s L := by
  haveI : Fact p₁.Prime := ⟨hp₁⟩
  haveI : Fact p₂.Prime := ⟨hp₂⟩
  haveI : Fact s.Prime := ⟨hs⟩
  have := offdiag_le (p₁ := p₁) (p₂ := p₂) (s := s) hp₁2 hp₂2 h12 h1s h2s
    (ZMod.unitOfCoprime a₁ ha₁) (ZMod.unitOfCoprime a₂ ha₂)
    (ZMod.unitOfCoprime b₁ (Nat.Coprime.pow_right 2 hb₁))
    (ZMod.unitOfCoprime b₂ (Nat.Coprime.pow_right 2 hb₂)) L
  simp only [ZMod.coe_unitOfCoprime] at this
  simp only [klNat_eq, offBound]
  exact this

/-- `Σ_m |z_m|² = |Σ_m z_m conj z_m|`. -/
theorem sum_norm_sq_eq_norm_sum (t : Finset ℕ) (z : ℕ → ℂ) :
    ∑ m ∈ t, ‖z m‖ ^ 2 = ‖∑ m ∈ t, z m * star (z m)‖ := by
  have h : ∑ m ∈ t, z m * star (z m) = ((∑ m ∈ t, ‖z m‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show star (z m) = starRingEnd ℂ (z m) from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **Bilinear bound for `Kl₃` over the moduli `p s²`.** Let `𝒫` be a set of odd primes and `𝒮` a set
of primes disjoint from `𝒫`. Let `u, v` be multipliers coprime to `p` and `s` respectively, and let
`α` be arbitrary coefficients. Put
`T = Σ_{s∈𝒮} Σ_{m≤L} α_m Σ_{p∈𝒫} K*(u m; p) K*(v m; s²)`. Then
`|T|² ≤ |𝒮| ‖α‖² Σ_s (Σ_p D(p, s) + Σ_{p₁≠p₂} O(p₁, p₂, s))`, where `D` is the diagonal bound
`9s⁴(L/p + 1)(2p√p + 1)²` and `O` the completed off-diagonal bound. Since
`Kl₃(am; ps²) = Kl₃(a s̄⁶ m; p) Kl₃(a p̄³ m; s²)`, this is Cauchy–Schwarz over `(s, m)` with the
`p`-sum kept inside, followed by completion modulo `p₁p₂s²`. -/
theorem norm_sq_factored_moduli_le (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hS : ∀ s ∈ S, s.Prime) (hPS : ∀ p ∈ P, ∀ s ∈ S, p ≠ s) (u v : ℕ → ℕ → ℕ)
    (hu : ∀ p ∈ P, ∀ s ∈ S, (u p s).Coprime p) (hv : ∀ p ∈ P, ∀ s ∈ S, (v p s).Coprime s)
    (α : ℕ → ℂ) (L : ℕ) :
    ‖∑ s ∈ S, ∑ m ∈ Finset.Icc 1 L,
        α m * ∑ p ∈ P, klNat p (u p s) m * klNat (s ^ 2) (v p s) m‖ ^ 2 ≤
      (S.card * ∑ m ∈ Finset.Icc 1 L, ‖α m‖ ^ 2) *
        ∑ s ∈ S, (∑ p ∈ P, diagBound p s L +
          ∑ p₁ ∈ P, ∑ p₂ ∈ P.erase p₁, offBound p₁ p₂ s L) := by
  classical
  set c : ℕ → ℕ → ℕ → ℂ := fun p s m => klNat p (u p s) m * klNat (s ^ 2) (v p s) m with hc
  set X : ℕ → ℕ → ℂ := fun s m => ∑ p ∈ P, c p s m with hX
  -- Cauchy–Schwarz over (s, m)
  have h1 : ‖∑ s ∈ S, ∑ m ∈ Finset.Icc 1 L, α m * X s m‖ ≤
      ∑ x ∈ S ×ˢ Finset.Icc 1 L, ‖α x.2‖ * ‖X x.1 x.2‖ := by
    rw [Finset.sum_product]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul]
  have h2 : ‖∑ s ∈ S, ∑ m ∈ Finset.Icc 1 L, α m * X s m‖ ^ 2 ≤
      (∑ x ∈ S ×ˢ Finset.Icc 1 L, ‖α x.2‖ ^ 2) *
        (∑ x ∈ S ×ˢ Finset.Icc 1 L, ‖X x.1 x.2‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have h3 : ∑ x ∈ S ×ˢ Finset.Icc 1 L, ‖α x.2‖ ^ 2 =
      S.card * ∑ m ∈ Finset.Icc 1 L, ‖α m‖ ^ 2 := by
    simp only [Finset.sum_product, Finset.sum_const, nsmul_eq_mul]
  -- the inner sum for each s
  have h4 : ∀ s ∈ S, ∑ m ∈ Finset.Icc 1 L, ‖X s m‖ ^ 2 ≤
      ∑ p ∈ P, diagBound p s L + ∑ p₁ ∈ P, ∑ p₂ ∈ P.erase p₁, offBound p₁ p₂ s L := by
    intro s hs
    have hexp : ∑ m ∈ Finset.Icc 1 L, X s m * star (X s m) =
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ m ∈ Finset.Icc 1 L, c p₁ s m * star (c p₂ s m) := by
      simp only [hX, star_sum, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p₁ _ => ?_
      rw [Finset.sum_comm]
    rw [sum_norm_sq_eq_norm_sum, hexp]
    refine (norm_sum_le _ _).trans ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p₁ hp₁ => ?_
    rw [← Finset.add_sum_erase _ _ hp₁]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [← sum_norm_sq_eq_norm_sum]
      exact diag_le_nat (hP p₁ hp₁).1 (hP p₁ hp₁).2 (hS s hs) (hu p₁ hp₁ s hs) (hv p₁ hp₁ s hs) L
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p₂ hp₂ => ?_)
      have hp₂' := Finset.mem_of_mem_erase hp₂
      exact offdiag_le_nat (hP p₁ hp₁).1 (hP p₂ hp₂').1 (hS s hs) (hP p₁ hp₁).2 (hP p₂ hp₂').2
        (Finset.ne_of_mem_erase hp₂).symm (hPS p₁ hp₁ s hs) (hPS p₂ hp₂' s hs)
        (hu p₁ hp₁ s hs) (hu p₂ hp₂' s hs) (hv p₁ hp₁ s hs) (hv p₂ hp₂' s hs) L
  calc ‖∑ s ∈ S, ∑ m ∈ Finset.Icc 1 L,
        α m * ∑ p ∈ P, klNat p (u p s) m * klNat (s ^ 2) (v p s) m‖ ^ 2
      = ‖∑ s ∈ S, ∑ m ∈ Finset.Icc 1 L, α m * X s m‖ ^ 2 := rfl
    _ ≤ (∑ x ∈ S ×ˢ Finset.Icc 1 L, ‖α x.2‖ ^ 2) *
        (∑ x ∈ S ×ˢ Finset.Icc 1 L, ‖X x.1 x.2‖ ^ 2) := h2
    _ ≤ (S.card * ∑ m ∈ Finset.Icc 1 L, ‖α m‖ ^ 2) *
        ∑ s ∈ S, (∑ p ∈ P, diagBound p s L +
          ∑ p₁ ∈ P, ∑ p₂ ∈ P.erase p₁, offBound p₁ p₂ s L) := by
        rw [h3, Finset.sum_product]
        gcongr with s hs
        exact h4 s hs

end

end GaloisForLFunctions.RHTower.HyperKloostermanFactoredModuli
