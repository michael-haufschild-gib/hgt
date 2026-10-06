import GaloisForLFunctions.RHTower.KuznetsovKloostermanSmallModulus
import GaloisForLFunctions.RHTower.KuznetsovGaussianTails
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# DI (1.27) with `N^ε`, and the envelope of `θ ↦ B(θ, c)` along `θ = ±cosh w`

For `B(θ, c) = Σ_{m,n ∈ (N,2N]} ᾱ_m α_n S(m, n; c) e(2θ√(mn)/c)` (`kloostermanPhaseForm`):

* for every `δ > 0`, `c ≤ N` and `1 ≤ |θ| ≤ 2`: `|B(θ, c)| ≤ C_δ √c N^{1/2+δ} Σ|α|²`
  (`exists_kloostermanPhaseForm_le_rpow`): Poisson (`exists_bilinear_kloosterman_small_le`) with the
  divisor bound for `c ≤ N^{1−δ/3}`, the separated form (1.26) above;
* for `c ≤ N` and `K ≥ 1`: `|B(±cosh w, c)| ≤ β + γ T_K(w)` with `β = C_δ √c N^{1/2+δ} Σ|α|²`,
  `γ = C₀(1 + N/c)(N + c) Σ|α|²` (`exists_envelope_le`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

open RHTower.Sieve DeckPointPair

noncomputable section

/-- `B(θ, c) = Σ_{m,n ∈ (N,2N]} ᾱ_m α_n S(m, n; c) e(2θ√(mn)/c)`. -/
def kloostermanPhaseForm (c : ℕ) [NeZero c] (N : ℕ) (α : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ m ∈ Finset.Ioc N (N + N), ∑ n ∈ Finset.Ioc N (N + N),
    conj (α m) * α n * kloostermanSum c (m : ZMod c) (n : ZMod c) *
      cexp (((2 * Real.pi * (2 * θ / c) * Real.sqrt ((m : ℝ) * n)) : ℝ) * I)

theorem continuous_kloostermanPhaseForm (c : ℕ) [NeZero c] (N : ℕ) (α : ℕ → ℂ) :
    Continuous (kloostermanPhaseForm c N α) := by
  unfold kloostermanPhaseForm
  fun_prop

theorem rpow_le_rpow_of_le_one {x a b : ℝ} (hx : 1 ≤ x) (hab : a ≤ b) : x ^ a ≤ x ^ b :=
  Real.rpow_le_rpow_of_exponent_le hx hab

/-- **DI (1.27)** with `N^ε`. -/
theorem exists_kloostermanPhaseForm_le_rpow {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℕ) [NeZero c] (N : ℕ), 1 ≤ N → c ≤ N → ∀ (α : ℕ → ℂ) (θ : ℝ), 1 ≤ |θ| → |θ| ≤ 2 →
      ‖kloostermanPhaseForm c N α θ‖ ≤
        C * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) * ∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2 := by
  set η := δ / 3 with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  set p := ⌈2 / η⌉₊ + 2
  have hp : 2 ≤ p := by simp only [p]; omega
  have hpη : 2 ≤ (p : ℝ) * η := by
    have h1 : 2 / η ≤ (⌈2 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (2 : ℝ) / η * η = 2 := by field_simp
    have h3 : ((⌈2 / η⌉₊ : ℕ) : ℝ) ≤ p := by simp only [p]; push_cast; linarith
    nlinarith
  obtain ⟨C₁, hC₁0, hsmall⟩ := exists_bilinear_kloosterman_small_le hp
  obtain ⟨C₀, hC₀0, hlarge⟩ := exists_bilinear_kloosterman_phase_le
  obtain ⟨D, hD0, hdiv⟩ := RHTower.card_divisors_le_const_mul_rpow hη
  set C' := C₁ * (D * (1 + 1 / η) + 1)
  refine ⟨max (Real.sqrt C') (6 * C₀), by positivity, fun c _ N hN hcN α θ hθ1 hθ2 => ?_⟩
  set A := ∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne c)
  have hc0 : (0 : ℝ) < c := by linarith
  have hcN' : (c : ℝ) ≤ N := by exact_mod_cast hcN
  have hsqc : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  by_cases hcut : (c : ℝ) ≤ (N : ℝ) ^ (1 - η)
  · -- Poisson range
    have hB := hsmall c N hN α θ hθ1 hθ2
    -- `(c/N)^p ≤ N^{-2}`
    have hratio : ((c : ℝ) / N) ^ p ≤ ((N : ℝ) ^ 2)⁻¹ := by
      have h1 : (c : ℝ) / N ≤ (N : ℝ) ^ (-η) := by
        rw [div_le_iff₀ hN0]
        calc (c : ℝ) ≤ (N : ℝ) ^ (1 - η) := hcut
          _ = (N : ℝ) ^ (-η) * N := by
              rw [show (1 : ℝ) - η = -η + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
      have h2 : ((c : ℝ) / N) ^ p ≤ ((N : ℝ) ^ (-η)) ^ p := pow_le_pow_left₀ (by positivity) h1 p
      have h3 : ((N : ℝ) ^ (-η)) ^ p = (N : ℝ) ^ (-(p * η)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
      have h4 : (N : ℝ) ^ (-(p * η)) ≤ (N : ℝ) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      have h5 : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ 2)⁻¹ := by
        rw [Real.rpow_neg hN0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      linarith
    have hpart : (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p ≤ c * N := by
      calc (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p ≤ (c : ℝ) ^ 2 * N ^ 2 * ((N : ℝ) ^ 2)⁻¹ := by
            gcongr
        _ = (c : ℝ) ^ 2 := by field_simp
        _ ≤ c * N := by nlinarith
    have hτ : (c.divisors.card : ℝ) ≤ D * (N : ℝ) ^ η := by
      calc (c.divisors.card : ℝ) ≤ D * (c : ℝ) ^ η := hdiv c (Nat.one_le_iff_ne_zero.2 (NeZero.ne c))
        _ ≤ D * (N : ℝ) ^ η := by gcongr
    have hlog : 1 + Real.log N ≤ (1 + 1 / η) * (N : ℝ) ^ η := by
      have h1 := Real.log_le_rpow_div hN0.le hη
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ η := Real.one_le_rpow hN1 hη.le
      have h3 : (N : ℝ) ^ η / η = 1 / η * (N : ℝ) ^ η := by ring
      nlinarith
    have hbig : (c : ℝ) * N * c.divisors.card * (1 + Real.log N) +
        (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p ≤ (D * (1 + 1 / η) + 1) * (c * (N : ℝ) ^ (1 + 2 * η)) := by
      have hNη : (N : ℝ) ^ (1 + 2 * η) = N * ((N : ℝ) ^ η * (N : ℝ) ^ η) := by
        rw [Real.rpow_add hN0, Real.rpow_one, ← Real.rpow_add hN0]; ring_nf
      have h1 : (c : ℝ) * N * c.divisors.card * (1 + Real.log N) ≤
          (c : ℝ) * N * (D * (N : ℝ) ^ η) * ((1 + 1 / η) * (N : ℝ) ^ η) := by
        have : 0 ≤ (c : ℝ) * N := by positivity
        have : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN1]
        gcongr
      have h2 : (c : ℝ) * N ≤ c * (N : ℝ) ^ (1 + 2 * η) := by
        gcongr
        exact Real.self_le_rpow_of_one_le hN1 (by linarith)
      rw [hNη] at h2 ⊢
      nlinarith
    have hsq : ‖kloostermanPhaseForm c N α θ‖ ^ 2 ≤ (Real.sqrt C' * Real.sqrt c *
        (N : ℝ) ^ (1 / 2 + η) * A) ^ 2 := by
      calc ‖kloostermanPhaseForm c N α θ‖ ^ 2
          ≤ C₁ * A ^ 2 * ((c : ℝ) * N * c.divisors.card * (1 + Real.log N) +
              (c : ℝ) ^ 2 * N ^ 2 * ((c : ℝ) / N) ^ p) := hB
        _ ≤ C₁ * A ^ 2 * ((D * (1 + 1 / η) + 1) * (c * (N : ℝ) ^ (1 + 2 * η))) := by gcongr
        _ = (Real.sqrt C' * Real.sqrt c * (N : ℝ) ^ (1 / 2 + η) * A) ^ 2 := by
            have e1 : Real.sqrt C' ^ 2 = C' := Real.sq_sqrt (by positivity)
            have e2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0.le
            have e3 : ((N : ℝ) ^ (1 / 2 + η)) ^ 2 = (N : ℝ) ^ (1 + 2 * η) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
            rw [mul_pow, mul_pow, mul_pow, e1, e2, e3]
            simp only [C']
            ring
    have hnn : 0 ≤ Real.sqrt C' * Real.sqrt c * (N : ℝ) ^ (1 / 2 + η) * A := by positivity
    calc ‖kloostermanPhaseForm c N α θ‖ ≤ Real.sqrt C' * Real.sqrt c * (N : ℝ) ^ (1 / 2 + η) * A :=
          (pow_le_pow_iff_left₀ (norm_nonneg _) hnn (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
      _ ≤ max (Real.sqrt C') (6 * C₀) * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) * A := by
          gcongr
          · exact le_max_left _ _
          · linarith
  · -- separated range
    push Not at hcut
    have hB := hlarge c N hN α θ
    have h1 : (1 : ℝ) + |θ| * N / c ≤ 3 * (N : ℝ) ^ η := by
      have hNc : (N : ℝ) / c ≤ (N : ℝ) ^ η := by
        rw [div_le_iff₀ hc0]
        calc (N : ℝ) = (N : ℝ) ^ η * (N : ℝ) ^ (1 - η) := by
              rw [← Real.rpow_add hN0, show η + (1 - η) = (1 : ℝ) by ring, Real.rpow_one]
          _ ≤ (N : ℝ) ^ η * c := by gcongr
      have h2 : (1 : ℝ) ≤ (N : ℝ) ^ η := Real.one_le_rpow hN1 hη.le
      have h3 : |θ| * N / c ≤ 2 * ((N : ℝ) / c) := by
        rw [mul_div_assoc]; gcongr
      linarith
    have h2 : (N : ℝ) + c ≤ 2 * N := by linarith
    have h3 : (N : ℝ) ^ (1 + η) ≤ Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) := by
      have hsc : (N : ℝ) ^ ((1 - η) / 2) ≤ Real.sqrt c := by
        rw [Real.sqrt_eq_rpow]
        calc (N : ℝ) ^ ((1 - η) / 2) = ((N : ℝ) ^ (1 - η)) ^ (1 / 2 : ℝ) := by
              rw [← Real.rpow_mul hN0.le]; ring_nf
          _ ≤ (c : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hcut.le (by norm_num)
      calc (N : ℝ) ^ (1 + η) = (N : ℝ) ^ ((1 - η) / 2) * (N : ℝ) ^ (1 / 2 + 3 * η / 2) := by
            rw [← Real.rpow_add hN0]; ring_nf
        _ ≤ Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) := by
            gcongr
            · linarith
    calc ‖kloostermanPhaseForm c N α θ‖
        ≤ C₀ * (1 + |θ| * N / c) * ((N : ℝ) + c) * A := hB
      _ ≤ C₀ * (3 * (N : ℝ) ^ η) * (2 * N) * A := by gcongr
      _ = 6 * C₀ * (N : ℝ) ^ (1 + η) * A := by
          rw [Real.rpow_add hN0, Real.rpow_one]; ring
      _ ≤ 6 * C₀ * (Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ)) * A := by gcongr
      _ ≤ max (Real.sqrt C') (6 * C₀) * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) * A := by
          rw [← mul_assoc]
          gcongr
          exact le_max_right _ _

theorem cosh_one_le_two : Real.cosh 1 ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  linarith

/-- **The envelope.** For `c ≤ N`, `K ≥ 1` and every `w`,
`|B(±cosh w, c)| ≤ C_δ √c N^{1/2+δ} Σ|α|² + C₀(1 + N/c)(N + c) Σ|α|² T_K(w)`. -/
theorem exists_envelope_le {δ : ℝ} (hδ : 0 < δ) : ∃ C C₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₀ ∧
    ∀ (c : ℕ) [NeZero c] (N : ℕ), 1 ≤ N → ∀ (α : ℕ → ℂ) (K : ℝ) (w : ℝ) (s : ℝ), (s = 1 ∨ s = -1) →
      ‖kloostermanPhaseForm c N α (s * Real.cosh w)‖ ≤
        (if c ≤ N then C * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) else 0) *
            ∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2 +
          C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * (∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2) *
            (if c ≤ N then tailFactor K w else 1 + Real.cosh w) := by
  obtain ⟨C, hC0, hC⟩ := exists_kloostermanPhaseForm_le_rpow hδ
  obtain ⟨C₀, hC₀0, hlarge⟩ := exists_bilinear_kloosterman_phase_le
  refine ⟨C, C₀, hC0, hC₀0.le, fun c _ N hN α K w s hs => ?_⟩
  set A := ∑ n ∈ Finset.Ioc N (N + N), ‖α n‖ ^ 2
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => by positivity
  have hc0 : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have habs : |s * Real.cosh w| = Real.cosh w := by
    rcases hs with rfl | rfl <;> simp [abs_of_pos (Real.cosh_pos w)]
  have hsep : ‖kloostermanPhaseForm c N α (s * Real.cosh w)‖ ≤
      C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * A * (1 + Real.cosh w) := by
    refine (hlarge c N hN α (s * Real.cosh w)).trans ?_
    rw [habs]
    have h1 : 1 + Real.cosh w * N / c ≤ (1 + (N : ℝ) / c) * (1 + Real.cosh w) := by
      have : 0 ≤ (N : ℝ) / c := by positivity
      have := Real.cosh_pos w
      rw [mul_div_assoc]
      nlinarith
    calc C₀ * (1 + Real.cosh w * N / c) * ((N : ℝ) + c) * A
        ≤ C₀ * ((1 + (N : ℝ) / c) * (1 + Real.cosh w)) * ((N : ℝ) + c) * A := by gcongr
      _ = _ := by ring
  have hnn : 0 ≤ C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * A := by positivity
  by_cases hcN : c ≤ N
  · rw [if_pos hcN, if_pos hcN]
    by_cases hw : |w| ≤ 1
    · have h1 : 1 ≤ |s * Real.cosh w| := by rw [habs]; exact Real.one_le_cosh w
      have h2 : |s * Real.cosh w| ≤ 2 := by
        rw [habs]
        calc Real.cosh w = Real.cosh |w| := (Real.cosh_abs w).symm
          _ ≤ Real.cosh 1 := Real.cosh_le_cosh.2 (by rw [abs_abs]; simpa using hw)
          _ ≤ 2 := cosh_one_le_two
      have := hC c N hN hcN α _ h1 h2
      have : 0 ≤ C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * A * tailFactor K w :=
        mul_nonneg hnn (tailFactor_nonneg K w)
      nlinarith
    · push Not at hw
      have h1 := one_add_cosh_le_tailFactor K hw.le
      have h2 : 0 ≤ C * Real.sqrt c * (N : ℝ) ^ (1 / 2 + δ) * A := by positivity
      calc ‖kloostermanPhaseForm c N α (s * Real.cosh w)‖
          ≤ C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * A * (1 + Real.cosh w) := hsep
        _ ≤ C₀ * (1 + (N : ℝ) / c) * ((N : ℝ) + c) * A * tailFactor K w := by gcongr
        _ ≤ _ := by nlinarith
  · rw [if_neg hcN, if_neg hcN, zero_mul, zero_add]
    exact hsep

end

end GaloisForLFunctions.RHTower.KuznetsovSeparation
