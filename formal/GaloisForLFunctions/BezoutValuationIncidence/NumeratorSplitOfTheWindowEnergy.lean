import GaloisForLFunctions.BezoutValuationIncidence.DiscreteGallagherInequalityAndTheWindowSpectrum

/-!
# The numerator split of the window energy

For a prime packet `c` on a set `S` of primes in `(2a₀, N]` the fluctuation is a sum over the Farey
fractions `a/p`:

`F_c(M) = Σ_{p ∈ S} Σ_{1 ≤ a < p} u(p, a) ω_p^{aM}`,  `u(p, a) = (c(p)/p) ω_p^a/(ω_p^a - 1)`,
`ω_p = e^{2πi/p}`.

Split the numerators at `a₀`. The small numerators `a ≤ a₀` and `p - a ≤ a₀` form the one-numerator sums

`Ψ_{±a}(M) = Σ_{p ∈ S} u(p, ±a) ω_p^{±aM}`,

and the large numerators form a trigonometric polynomial over response frequencies whose coefficients
are small: `|ω_p^a - 1| = 2 sin(πa/p) ≥ 4 min(a, p-a)/p` gives `Σ_{large} |u|² ≤ Σ_p c(p)²/(8a₀)`. The
log-free large sieve bounds the large part on any window, and Cauchy–Schwarz with weights `1/a` bounds
the small part. With `h_{a₀} = Σ_{a ≤ a₀} 1/a`, for `1 ≤ X`,

`Σ_{X ≤ M < X+K} F_c(M)²/(M(M+1)) ≤ (2/X²) (2 h_{a₀} Σ_{a ≤ a₀} a Σ_M (|Ψ_a(M)|² + |Ψ_{-a}(M)|²)
  + (K + 2N² - 1) Σ_p c(p)²/(8a₀))`.

Relative to the window diagonal `≍ Σ_p c(p)²/X`, the large numerators cost `≍ (K + N²)/(a₀ X)`. On a
dyadic window `[X, 2X)` below the quadratic horizon only the numerators `a ≲ P²/X` matter, and the
Gallagher clusters of `Ψ_{±a}` are sliding interval sums of `c` over intervals of length `≍ P²/(aX)`.
At exponents `θ` just above one, a bounded number of numerators carries all of the energy.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Prime roots as powers -/

theorem primitiveRoots_prime_eq_image {p : ℕ} (hp : p.Prime) :
    primitiveRoots p ℂ = (Ico 1 p).image (fun a => stdRoot p ^ a) := by
  rw [← nontrivialRoots_eq_image hp.pos]
  ext ζ
  rw [mem_primitiveRoots hp.pos, mem_nontrivialRoots hp.pos]
  constructor
  · intro h; exact ⟨h.ne_one hp.one_lt, h.pow_eq_one⟩
  · rintro ⟨h1, hpow⟩
    haveI := Fact.mk hp
    exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hpow h1)

theorem stdRoot_pow_injOn {p : ℕ} (hp : 0 < p) :
    Set.InjOn (fun a => stdRoot p ^ a) (Ico 1 p : Set ℕ) := fun _ hi _ hj h =>
  (Complex.isPrimitiveRoot_exp p hp.ne').pow_inj (Finset.mem_Ico.mp hi).2 (Finset.mem_Ico.mp hj).2 h

theorem orderOf_stdRoot_pow {p a : ℕ} (hp : p.Prime) (ha : a ∈ Ico 1 p) :
    orderOf (stdRoot p ^ a) = p := by
  have h : stdRoot p ^ a ∈ primitiveRoots p ℂ := by
    rw [primitiveRoots_prime_eq_image hp]; exact mem_image_of_mem _ ha
  exact ((mem_primitiveRoots hp.pos).mp h).eq_orderOf.symm

/-- The Farey coefficient `u(p, a) = (c(p)/p) ω_p^a/(ω_p^a - 1)`. -/
def fareyCoeff (c : ℕ → ℝ) (p a : ℕ) : ℂ :=
  ((c p / p : ℝ) : ℂ) * (stdRoot p ^ a / (stdRoot p ^ a - 1))

theorem rowFluct_prime_eq_farey {N : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N)
    {c : ℕ → ℝ} (hsupp : ∀ n, c n ≠ 0 → n ∈ S) (M : ℕ) :
    (rowFluct N c M : ℂ) = ∑ p ∈ S, ∑ a ∈ Ico 1 p, fareyCoeff c p a * (stdRoot p ^ a) ^ M := by
  rw [rowFluct_eq_spectral hS hsupp]
  refine sum_congr rfl fun p hp => ?_
  rw [primitiveRoots_prime_eq_image (hS p hp).1, sum_image (stdRoot_pow_injOn (hS p hp).1.pos)]
  exact sum_congr rfl fun a _ => by simp only [fareyCoeff]

/-! ## §2. The split -/

/-- The one-numerator sums `Ψ_a(M) = Σ_p u(p, a) ω_p^{aM}` and `Ψ_{-a}(M) = Σ_p u(p, p-a) ω_p^{(p-a)M}`. -/
def numeratorSum (S : Finset ℕ) (c : ℕ → ℝ) (a M : ℕ) : ℂ :=
  ∑ p ∈ S, fareyCoeff c p a * (stdRoot p ^ a) ^ M

def conjNumeratorSum (S : Finset ℕ) (c : ℕ → ℝ) (a M : ℕ) : ℂ :=
  ∑ p ∈ S, fareyCoeff c p (p - a) * (stdRoot p ^ (p - a)) ^ M

/-- The large-numerator part. -/
def largeNumeratorPart (S : Finset ℕ) (c : ℕ → ℝ) (a₀ M : ℕ) : ℂ :=
  ∑ p ∈ S, ∑ a ∈ Ico (a₀ + 1) (p - a₀), fareyCoeff c p a * (stdRoot p ^ a) ^ M

theorem rowFluct_eq_numerator_split {N a₀ : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ 2 * a₀ < p) {c : ℕ → ℝ} (hsupp : ∀ n, c n ≠ 0 → n ∈ S)
    (M : ℕ) :
    (rowFluct N c M : ℂ) = ∑ a ∈ Ico 1 (a₀ + 1), (numeratorSum S c a M + conjNumeratorSum S c a M) +
      largeNumeratorPart S c a₀ M := by
  rw [rowFluct_prime_eq_farey (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩) hsupp]
  simp only [numeratorSum, conjNumeratorSum, largeNumeratorPart, sum_add_distrib]
  rw [sum_comm (s := Ico 1 (a₀ + 1)), sum_comm (s := Ico 1 (a₀ + 1)), ← sum_add_distrib,
    ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  have hp2 := (hS p hp).2.2
  rw [← sum_Ico_consecutive _ (by omega : 1 ≤ a₀ + 1) (by omega : a₀ + 1 ≤ p),
    ← sum_Ico_consecutive _ (by omega : a₀ + 1 ≤ p - a₀) (by omega : p - a₀ ≤ p)]
  have hrefl : ∑ b ∈ Ico (p - a₀) p, fareyCoeff c p b * (stdRoot p ^ b) ^ M =
      ∑ a ∈ Ico 1 (a₀ + 1), fareyCoeff c p (p - a) * (stdRoot p ^ (p - a)) ^ M := by
    refine sum_nbij' (fun b => p - b) (fun a => p - a) ?_ ?_ ?_ ?_ ?_
    · intro b hb; have := mem_Ico.mp hb; exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro a ha; have := mem_Ico.mp ha; exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro b hb; have := mem_Ico.mp hb; omega
    · intro a ha; have := mem_Ico.mp ha; omega
    · intro b hb; have := mem_Ico.mp hb; rw [show p - (p - b) = b by omega]
  rw [hrefl]
  ring

/-! ## §3. The large numerators -/

theorem sum_Ico_inv_sq_le {a₀ : ℕ} (ha₀ : 1 ≤ a₀) (B : ℕ) :
    ∑ a ∈ Ico (a₀ + 1) B, 1 / (a : ℝ) ^ 2 ≤ 1 / (a₀ : ℝ) := by
  rcases le_or_gt B (a₀ + 1) with hB | hB
  · rw [Ico_eq_empty_of_le hB, sum_empty]; positivity
  have key : ∀ B, a₀ + 1 ≤ B →
      ∑ a ∈ Ico (a₀ + 1) B, 1 / (a : ℝ) ^ 2 ≤ 1 / (a₀ : ℝ) - 1 / ((B : ℝ) - 1) := by
    intro B hB'
    induction B, hB' using Nat.le_induction with
    | base => simp
    | succ B hB ih =>
      rw [sum_Ico_succ_top hB]
      have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast (by omega : 2 ≤ B)
      have hstep : 1 / (B : ℝ) ^ 2 ≤ 1 / ((B : ℝ) - 1) - 1 / ((B + 1 : ℕ) - 1 : ℝ) := by
        push_cast
        rw [add_sub_cancel_right, div_sub_div _ _ (by linarith) (by linarith),
          div_le_div_iff₀ (by positivity) (by nlinarith)]
        nlinarith
      linarith
  have h := key B hB.le
  have : 0 ≤ 1 / ((B : ℝ) - 1) := by
    have : (1 : ℝ) ≤ (B : ℝ) - 1 := by
      have : (a₀ + 2 : ℕ) ≤ B := by omega
      have : ((a₀ + 2 : ℕ) : ℝ) ≤ B := by exact_mod_cast this
      push_cast at this; linarith [(by exact_mod_cast ha₀ : (1 : ℝ) ≤ a₀)]
    positivity
  linarith

/-- `|ω_p^a - 1|^{-2} ≤ (p²/16)(1/a² + 1/(p-a)²)` for `1 ≤ a < p`. -/
theorem inv_norm_stdRoot_pow_sub_one_sq_le {p a : ℕ} (hp : 0 < p) (ha : a ∈ Ico 1 p) :
    1 / ‖stdRoot p ^ a - 1‖ ^ 2 ≤ (p : ℝ) ^ 2 / 16 * (1 / (a : ℝ) ^ 2 + 1 / ((p - a : ℕ) : ℝ) ^ 2) := by
  have ha' := mem_Ico.mp ha
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set m : ℕ := min a (p - a)
  have hm1 : 1 ≤ m := le_min ha'.1 (by omega)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hsin := two_mul_le_sin_pi_mul (β := (a : ℝ) / p) (δ := (m : ℝ) / p) (by positivity)
    (by rw [div_le_div_iff_of_pos_right hpR]; exact_mod_cast min_le_left _ _)
    (by
      rw [show (1 : ℝ) - (m : ℝ) / p = ((p : ℝ) - m) / p by field_simp]
      rw [div_le_div_iff_of_pos_right hpR]
      have : (m : ℝ) ≤ ((p - a : ℕ) : ℝ) := by exact_mod_cast min_le_right _ _
      rw [Nat.cast_sub ha'.2.le] at this; linarith)
  have hnorm : ‖stdRoot p ^ a - 1‖ ^ 2 = 4 * Real.sin (Real.pi * ((a : ℝ) / p)) ^ 2 := by
    rw [norm_stdRoot_pow_sub_one_sq]; ring_nf
  have hlow : 16 * (m : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ ‖stdRoot p ^ a - 1‖ ^ 2 := by
    rw [hnorm]
    have h2 : 0 ≤ 2 * ((m : ℝ) / p) := by positivity
    have := pow_le_pow_left₀ h2 hsin 2
    field_simp at this ⊢
    nlinarith
  calc 1 / ‖stdRoot p ^ a - 1‖ ^ 2 ≤ 1 / (16 * (m : ℝ) ^ 2 / (p : ℝ) ^ 2) :=
        one_div_le_one_div_of_le (by positivity) hlow
    _ = (p : ℝ) ^ 2 / 16 * (1 / (m : ℝ) ^ 2) := by field_simp
    _ ≤ (p : ℝ) ^ 2 / 16 * (1 / (a : ℝ) ^ 2 + 1 / ((p - a : ℕ) : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total a (p - a) with h | h
        · have : m = a := min_eq_left h
          rw [this]; have : 0 ≤ 1 / ((p - a : ℕ) : ℝ) ^ 2 := by positivity
          linarith
        · have : m = p - a := min_eq_right h
          rw [this]; have : 0 ≤ 1 / (a : ℝ) ^ 2 := by positivity
          linarith

/-- The large-numerator frequencies `ω_p^a`, `a₀ < a < p - a₀`. -/
def largeFreqs (S : Finset ℕ) (a₀ : ℕ) : Finset ℂ :=
  S.biUnion fun p => (Ico (a₀ + 1) (p - a₀)).image fun a => stdRoot p ^ a

/-- The coefficient `ζ ↦ (c(ord ζ)/ord ζ) ζ/(ζ - 1)` of the prime spectrum. -/
def primeSpectrumCoeff (c : ℕ → ℝ) (ζ : ℂ) : ℂ :=
  ((c (orderOf ζ) / orderOf ζ : ℝ) : ℂ) * (ζ / (ζ - 1))

theorem sum_largeFreqs {β : Type*} [AddCommMonoid β] {a₀ : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (g : ℂ → β) :
    ∑ ζ ∈ largeFreqs S a₀, g ζ = ∑ p ∈ S, ∑ a ∈ Ico (a₀ + 1) (p - a₀), g (stdRoot p ^ a) := by
  classical
  rw [largeFreqs, sum_biUnion]
  · refine sum_congr rfl fun p hp => ?_
    rw [sum_image]
    intro i hi j hj h
    have hi' := mem_Ico.mp hi
    have hj' := mem_Ico.mp hj
    have hi1 : i ∈ (Ico 1 p : Set ℕ) := Finset.mem_coe.mpr (mem_Ico.mpr ⟨by omega, by omega⟩)
    have hj1 : j ∈ (Ico 1 p : Set ℕ) := Finset.mem_coe.mpr (mem_Ico.mpr ⟨by omega, by omega⟩)
    exact stdRoot_pow_injOn (hS p hp).pos hi1 hj1 h
  · intro p hp p' hp' hpp'
    rw [Function.onFun, disjoint_left]
    intro ζ hζ hζ'
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hζ
    obtain ⟨a', ha', heq⟩ := mem_image.mp hζ'
    have hal := mem_Ico.mp ha
    have hal' := mem_Ico.mp ha'
    have hI : a ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
    have hI' : a' ∈ Ico 1 p' := mem_Ico.mpr ⟨by omega, by omega⟩
    have h1 := orderOf_stdRoot_pow (hS p hp) hI
    have h2 := orderOf_stdRoot_pow (hS p' hp') hI'
    rw [heq] at h2
    exact (hpp' (h1.symm.trans h2)).elim

theorem largeNumeratorPart_eq {a₀ : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (c : ℕ → ℝ) (M : ℕ) :
    largeNumeratorPart S c a₀ M = ∑ ζ ∈ largeFreqs S a₀, primeSpectrumCoeff c ζ * ζ ^ M := by
  rw [sum_largeFreqs hS, largeNumeratorPart]
  refine sum_congr rfl fun p hp => sum_congr rfl fun a ha => ?_
  have ha' := mem_Ico.mp ha
  rw [primeSpectrumCoeff, orderOf_stdRoot_pow (hS p hp) (mem_Ico.mpr ⟨by omega, by omega⟩),
    fareyCoeff]

theorem largeFreqs_subset {N a₀ : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) :
    largeFreqs S a₀ ⊆ responseRoots N := by
  intro ζ hζ
  obtain ⟨p, hp, hζp⟩ := mem_biUnion.mp hζ
  obtain ⟨a, _, rfl⟩ := mem_image.mp hζp
  have hp0 := (hS p hp).1.pos
  have hω : IsPrimitiveRoot (stdRoot p) p := Complex.isPrimitiveRoot_exp p hp0.ne'
  refine mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨hp0, (hS p hp).2⟩, ?_⟩
  rw [Polynomial.mem_nthRootsFinset hp0, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]

/-- The large numerators carry little mass: `Σ_{large} |u|² ≤ Σ_p c(p)²/(8a₀)`. -/
theorem sum_largeFreqs_norm_sq_le {a₀ : ℕ} {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ 2 * a₀ < p)
    (ha₀ : 1 ≤ a₀) (c : ℕ → ℝ) :
    ∑ ζ ∈ largeFreqs S a₀, ‖primeSpectrumCoeff c ζ‖ ^ 2 ≤ ∑ p ∈ S, c p ^ 2 / (8 * a₀) := by
  rw [sum_largeFreqs (a₀ := a₀) (fun p hp => (hS p hp).1)
    (fun ζ => ‖primeSpectrumCoeff c ζ‖ ^ 2)]
  refine sum_le_sum fun p hp => ?_
  have hp' := hS p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
  have ha₀R : (1 : ℝ) ≤ a₀ := by exact_mod_cast ha₀
  have hterm : ∀ a ∈ Ico (a₀ + 1) (p - a₀), ‖primeSpectrumCoeff c (stdRoot p ^ a)‖ ^ 2 ≤
      c p ^ 2 / 16 * (1 / (a : ℝ) ^ 2 + 1 / ((p - a : ℕ) : ℝ) ^ 2) := by
    intro a ha
    have ha' := mem_Ico.mp ha
    have haI : a ∈ Ico 1 p := mem_Ico.mpr ⟨by omega, by omega⟩
    have hn : ‖stdRoot p ^ a‖ = 1 := by rw [stdRoot_pow, mul_comm, Complex.norm_exp_ofReal_mul_I]
    have hmem : stdRoot p ^ a ∈ nontrivialRoots p := by
      rw [nontrivialRoots_eq_image hp'.1.pos]; exact mem_image_of_mem _ haI
    have hne : stdRoot p ^ a - 1 ≠ 0 := sub_ne_zero.mpr ((mem_nontrivialRoots hp'.1.pos).mp hmem).1
    rw [primeSpectrumCoeff, orderOf_stdRoot_pow hp'.1 haI, norm_mul, norm_div, hn, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs, one_div_pow]
    have h := inv_norm_stdRoot_pow_sub_one_sq_le hp'.1.pos haI
    calc (c p / p) ^ 2 * (1 / ‖stdRoot p ^ a - 1‖ ^ 2)
        ≤ (c p / p) ^ 2 * ((p : ℝ) ^ 2 / 16 * (1 / (a : ℝ) ^ 2 + 1 / ((p - a : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = c p ^ 2 / 16 * (1 / (a : ℝ) ^ 2 + 1 / ((p - a : ℕ) : ℝ) ^ 2) := by field_simp
  have hrefl : ∑ a ∈ Ico (a₀ + 1) (p - a₀), 1 / ((p - a : ℕ) : ℝ) ^ 2 =
      ∑ a ∈ Ico (a₀ + 1) (p - a₀), 1 / (a : ℝ) ^ 2 := by
    refine sum_nbij' (fun a => p - a) (fun a => p - a) ?_ ?_ ?_ ?_ ?_
    · intro a ha; have := mem_Ico.mp ha; exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro a ha; have := mem_Ico.mp ha; exact mem_Ico.mpr ⟨by omega, by omega⟩
    · intro a ha; have := mem_Ico.mp ha; omega
    · intro a ha; have := mem_Ico.mp ha; omega
    · intro a _; rfl
  have htail := sum_Ico_inv_sq_le ha₀ (p - a₀)
  calc ∑ a ∈ Ico (a₀ + 1) (p - a₀), ‖primeSpectrumCoeff c (stdRoot p ^ a)‖ ^ 2
      ≤ ∑ a ∈ Ico (a₀ + 1) (p - a₀), c p ^ 2 / 16 * (1 / (a : ℝ) ^ 2 + 1 / ((p - a : ℕ) : ℝ) ^ 2) :=
        sum_le_sum hterm
    _ = c p ^ 2 / 16 * (2 * ∑ a ∈ Ico (a₀ + 1) (p - a₀), 1 / (a : ℝ) ^ 2) := by
        rw [← mul_sum, sum_add_distrib, hrefl]; ring
    _ ≤ c p ^ 2 / 16 * (2 * (1 / (a₀ : ℝ))) := by gcongr
    _ = c p ^ 2 / (8 * a₀) := by field_simp; ring

/-! ## §4. The window energy -/

/-- **The numerator split of the window energy.** For a prime packet `c` on `S ⊆ (2a₀, N]`,
`2 ≤ N`, `1 ≤ a₀`, `1 ≤ X`, with `h_{a₀} = Σ_{a ≤ a₀} 1/a`,
`Σ_{X ≤ M < X+K} F_c(M)²/(M(M+1)) ≤ (2/X²)(2 h_{a₀} Σ_{a ≤ a₀} a Σ_M (|Ψ_a(M)|² + |Ψ_{-a}(M)|²)
  + (K + 2N² - 1) Σ_p c(p)²/(8a₀))`. -/
theorem window_energy_le_numerator_split {N a₀ X K : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ 2 * a₀ < p) (hN : 2 ≤ N) (ha₀ : 1 ≤ a₀) (hX : 1 ≤ X)
    {c : ℕ → ℝ} (hsupp : ∀ n, c n ≠ 0 → n ∈ S) :
    ∑ j ∈ range K, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ) ≤
      2 / (X : ℝ) ^ 2 * (2 * (∑ a ∈ Ico 1 (a₀ + 1), 1 / (a : ℝ)) *
          ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * ∑ j ∈ range K,
            (‖numeratorSum S c a (X + j)‖ ^ 2 + ‖conjNumeratorSum S c a (X + j)‖ ^ 2) +
        ((K : ℝ) + 2 * (N : ℝ) ^ 2 - 1) * ∑ p ∈ S, c p ^ 2 / (8 * a₀)) := by
  set h := ∑ a ∈ Ico 1 (a₀ + 1), 1 / (a : ℝ)
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hh : 0 < h := by
    have : 1 / ((1 : ℕ) : ℝ) ≤ h :=
      single_le_sum (f := fun a : ℕ => 1 / (a : ℝ)) (fun _ _ => by positivity)
        (mem_Ico.mpr ⟨le_rfl, by omega⟩)
    norm_num at this; linarith
  -- pointwise split
  have hpt : ∀ M, rowFluct N c M ^ 2 ≤ 2 * (h * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) *
      (2 * (‖numeratorSum S c a M‖ ^ 2 + ‖conjNumeratorSum S c a M‖ ^ 2))) +
      2 * ‖largeNumeratorPart S c a₀ M‖ ^ 2 := by
    intro M
    have hsplit := rowFluct_eq_numerator_split hS hsupp M
    have hn : rowFluct N c M ^ 2 = ‖(rowFluct N c M : ℂ)‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hn, hsplit]
    set Fs := ∑ a ∈ Ico 1 (a₀ + 1), (numeratorSum S c a M + conjNumeratorSum S c a M)
    have h2 : ‖Fs + largeNumeratorPart S c a₀ M‖ ^ 2 ≤
        2 * ‖Fs‖ ^ 2 + 2 * ‖largeNumeratorPart S c a₀ M‖ ^ 2 := by
      have hadd := norm_add_le Fs (largeNumeratorPart S c a₀ M)
      calc ‖Fs + largeNumeratorPart S c a₀ M‖ ^ 2
          ≤ (‖Fs‖ + ‖largeNumeratorPart S c a₀ M‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hadd 2
        _ ≤ 2 * ‖Fs‖ ^ 2 + 2 * ‖largeNumeratorPart S c a₀ M‖ ^ 2 := by
          nlinarith [sq_nonneg (‖Fs‖ - ‖largeNumeratorPart S c a₀ M‖)]
    have hFs : ‖Fs‖ ^ 2 ≤ h * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) *
        (2 * (‖numeratorSum S c a M‖ ^ 2 + ‖conjNumeratorSum S c a M‖ ^ 2)) := by
      set z : ℕ → ℝ := fun a => ‖numeratorSum S c a M‖ + ‖conjNumeratorSum S c a M‖
      have hz : ‖Fs‖ ≤ ∑ a ∈ Ico 1 (a₀ + 1), z a :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_add_le _ _)
      have htitu := Finset.sq_sum_div_le_sum_sq_div (Ico 1 (a₀ + 1)) z
        (g := fun a => 1 / (a : ℝ)) (fun a ha => by have := (mem_Ico.mp ha).1; positivity)
      rw [div_le_iff₀ hh] at htitu
      have hz0 : 0 ≤ ∑ a ∈ Ico 1 (a₀ + 1), z a := sum_nonneg fun a _ => by positivity
      calc ‖Fs‖ ^ 2 ≤ (∑ a ∈ Ico 1 (a₀ + 1), z a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
        _ ≤ (∑ a ∈ Ico 1 (a₀ + 1), z a ^ 2 / (1 / (a : ℝ))) * h := htitu
        _ ≤ h * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) *
              (2 * (‖numeratorSum S c a M‖ ^ 2 + ‖conjNumeratorSum S c a M‖ ^ 2)) := by
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun a ha => ?_) hh.le
          have := (mem_Ico.mp ha).1
          simp only [z]
          rw [div_div_eq_mul_div, div_one]
          nlinarith [sq_nonneg (‖numeratorSum S c a M‖ - ‖conjNumeratorSum S c a M‖),
            (by positivity : (0 : ℝ) ≤ a)]
    linarith
  have hw : ∀ j, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ) ≤
      1 / (X : ℝ) ^ 2 * rowFluct N c (X + j) ^ 2 := by
    intro j
    rw [div_eq_mul_one_div, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hp : (X : ℝ) ^ 2 ≤ (pronicSeq (X + j) : ℝ) := by
      rw [pronicSeq]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) j]
    exact one_div_le_one_div_of_le (by positivity) hp
  -- the large-numerator window energy
  have hlarge : ∑ j ∈ range K, ‖largeNumeratorPart S c a₀ (X + j)‖ ^ 2 ≤
      ((K : ℝ) + 2 * (N : ℝ) ^ 2 - 1) * ∑ p ∈ S, c p ^ 2 / (8 * a₀) := by
    have hre : ∑ j ∈ range K, ‖largeNumeratorPart S c a₀ (X + j)‖ ^ 2 =
        ∑ k ∈ Icc ((X - 1) + 1) ((X - 1) + K),
          ‖∑ ζ ∈ largeFreqs S a₀, primeSpectrumCoeff c ζ * ζ ^ k‖ ^ 2 := by
      rw [show (X - 1) + 1 = X by omega]
      rw [show Icc X (X - 1 + K) = Ico X (X + K) by ext; simp only [mem_Icc, mem_Ico]; omega,
        sum_Ico_eq_sum_range, show X + K - X = K by omega]
      exact sum_congr rfl fun j _ => by
        rw [largeNumeratorPart_eq (a₀ := a₀) (S := S) (fun p hp => (hS p hp).1)]
    rw [hre]
    have hsand := abs_window_sum_norm_sq_sub_le hN
      (largeFreqs_subset (a₀ := a₀) fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)
      (primeSpectrumCoeff c) (X - 1) K
    have hmass := sum_largeFreqs_norm_sq_le (fun p hp => ⟨(hS p hp).1, (hS p hp).2.2⟩) ha₀ c
    have hC : (0 : ℝ) ≤ (K : ℝ) + 2 * (N : ℝ) ^ 2 - 1 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      nlinarith
    have h1 := (abs_le.mp hsand).2
    have hm0 : 0 ≤ ∑ ζ ∈ largeFreqs S a₀, ‖primeSpectrumCoeff c ζ‖ ^ 2 :=
      sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hmass hC]
  calc ∑ j ∈ range K, rowFluct N c (X + j) ^ 2 / (pronicSeq (X + j) : ℝ)
      ≤ ∑ j ∈ range K, 1 / (X : ℝ) ^ 2 * (2 * (h * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) *
          (2 * (‖numeratorSum S c a (X + j)‖ ^ 2 + ‖conjNumeratorSum S c a (X + j)‖ ^ 2))) +
          2 * ‖largeNumeratorPart S c a₀ (X + j)‖ ^ 2) :=
        sum_le_sum fun j _ => (hw j).trans (mul_le_mul_of_nonneg_left (hpt _) (by positivity))
    _ = 2 / (X : ℝ) ^ 2 * (2 * h * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * ∑ j ∈ range K,
            (‖numeratorSum S c a (X + j)‖ ^ 2 + ‖conjNumeratorSum S c a (X + j)‖ ^ 2) +
          ∑ j ∈ range K, ‖largeNumeratorPart S c a₀ (X + j)‖ ^ 2) := by
        set x : ℕ → ℕ → ℝ := fun a j =>
          ‖numeratorSum S c a (X + j)‖ ^ 2 + ‖conjNumeratorSum S c a (X + j)‖ ^ 2
        set y : ℕ → ℝ := fun j => ‖largeNumeratorPart S c a₀ (X + j)‖ ^ 2
        have hin : ∀ j, ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * (2 * x a j) =
            2 * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * x a j := fun j => by
          rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
        have hswap : ∑ j ∈ range K, ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * x a j =
            ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * ∑ j ∈ range K, x a j := by
          rw [sum_comm]; exact sum_congr rfl fun a _ => by rw [mul_sum]
        calc ∑ j ∈ range K, 1 / (X : ℝ) ^ 2 * (2 * (h * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * (2 * x a j)) +
              2 * y j)
            = ∑ j ∈ range K, (4 * h / (X : ℝ) ^ 2 * ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * x a j +
                2 / (X : ℝ) ^ 2 * y j) := sum_congr rfl fun j _ => by rw [hin]; ring
          _ = 4 * h / (X : ℝ) ^ 2 * ∑ j ∈ range K, ∑ a ∈ Ico 1 (a₀ + 1), (a : ℝ) * x a j +
                2 / (X : ℝ) ^ 2 * ∑ j ∈ range K, y j := by
              rw [sum_add_distrib, ← mul_sum, ← mul_sum]
          _ = _ := by rw [hswap]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hlarge) (by positivity)

end

end GaloisForLFunctions.BezoutValuationIncidence
