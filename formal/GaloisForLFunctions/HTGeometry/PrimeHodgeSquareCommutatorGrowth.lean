import GaloisForLFunctions.HTGeometry.PrimeFormationSmallApertureLaw
import GaloisForLFunctions.HTGeometry.PrimeHodgeCubicSylvesterLaw
import GaloisForLFunctions.RHTower.CommonRadialSubunitHarmonicCompletion

/-!
# The finite-capital square is not source-invariant

The normalized Stokes prime kernel has the coherence form
`A_d(p,q) = √(μ_d(p)μ_d(q)) c(λ_p, λ_q)³` with `c(s,t) = 2√(st)/(s+t)`; every entry is strictly
positive (**(PCOB.7)–(PCOB.8)**), and the square has the entries
`A_d²(p,q) = √(μ_d(p)μ_d(q)) Σ_r μ_d(r) c(λ_p,λ_r)³ c(λ_r,λ_q)³` (**(PCOB.28)**).

Take the logarithmic blocks `1 < dλ_p ≤ 2`, `2 < dλ_r ≤ 3`, `4 < dλ_q ≤ 5`.  On them `c ≥ 1/5` and
`|λ_p - λ_q| > 2/d`, while the small-aperture law gives every block a positive limiting mass.
Hence the Hilbert–Schmidt mass of the commutator `[L, A_d²]`, `L e_p = λ_p e_p`, is at least
`c₀/d²` (**(PCOB.29)**), and the same holds, with the factor `w₀⁴`, for the commutator of
`𝖳_d² = Φ² ⊗ A_d²` with `I ⊗ L`; in particular that mass is unbounded as `d → 0+`
(**(PCOB.30)**).  The Hilbert–Schmidt mass of an operator is computed from its matrix in the
prime basis, `Σ_{p,q} |⟨e_p, X e_q⟩|²`, in `[0, ∞]`.
-/

open Filter Topology Set
open scoped ComplexOrder ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower GaloisForLFunctions

local notation "ℓ²P" => lp (fun _ : Nat.Primes => ℂ) 2

variable {d : ℝ}

/-! ## The coherence form of the Stokes kernel -/

/-- The coherence `c(s,t) = 2√(st)/(s+t)` of two prime clocks. -/
def apertureCoherence (s t : ℝ) : ℝ := 2 * Real.sqrt (s * t) / (s + t)

theorem apertureCoherence_pos {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : 0 < apertureCoherence s t :=
  div_pos (mul_pos two_pos (Real.sqrt_pos.2 (mul_pos hs ht))) (add_pos hs ht)

theorem apertureCoherence_le_one {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : apertureCoherence s t ≤ 1 := by
  rw [apertureCoherence, div_le_one (add_pos hs ht), Real.sqrt_mul hs.le]
  nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt t), Real.sq_sqrt hs.le, Real.sq_sqrt ht.le]

/-- On logarithmic blocks inside `(1, 5]` the coherence is at least `1/5`. -/
theorem apertureCoherence_ge {s t : ℝ} (hd : 0 < d) (hs : 1 < d * s) (hs' : d * s ≤ 5)
    (ht : 1 < d * t) (ht' : d * t ≤ 5) : 1 / 5 ≤ apertureCoherence s t := by
  have hs0 : 0 < s := pos_of_mul_pos_right (by linarith) hd.le
  have ht0 : 0 < t := pos_of_mul_pos_right (by linarith) hd.le
  have hsq : 1 / d ≤ Real.sqrt (s * t) := by
    rw [show 1 / d = Real.sqrt ((1 / d) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    have h1 : 1 / d < s := by rw [div_lt_iff₀ hd]; linarith
    have h2 : 1 / d < t := by rw [div_lt_iff₀ hd]; linarith
    nlinarith [div_pos one_pos hd]
  rw [apertureCoherence, le_div_iff₀ (add_pos hs0 ht0)]
  have h3 : d * (s + t) ≤ 10 := by linarith
  have h4 : 1 ≤ d * Real.sqrt (s * t) := by
    rw [div_le_iff₀ hd] at hsq
    linarith
  nlinarith

/-- The real Stokes entry `√(μ_d(p)μ_d(q)) c(λ_p, λ_q)³`. -/
def stokesEntry (d : ℝ) (p q : Nat.Primes) : ℝ :=
  Real.sqrt (primeFormationLaw d p * primeFormationLaw d q) *
    apertureCoherence (Real.log (p : ℝ)) (Real.log (q : ℝ)) ^ 3

theorem stokesEntry_pos (hd : 0 < d) (p q : Nat.Primes) : 0 < stokesEntry d p q :=
  mul_pos (Real.sqrt_pos.2 (mul_pos (primeFormationLaw_pos hd p) (primeFormationLaw_pos hd q)))
    (pow_pos (apertureCoherence_pos (primeClock_pos p) (primeClock_pos q)) 3)

/-- The PCOB source vector is the real vector `b_d(p) = √(μ_d(p) λ_p³)`. -/
theorem primeHodgeCubicBirthVector_eq_sqrt (hd : 0 < d) (p : Nat.Primes) :
    primeHodgeCubicBirthVector d p =
      ((Real.sqrt (primeFormationLaw d p * Real.log (p : ℝ) ^ 3) : ℝ) : ℂ) := by
  have key : ∀ x y : ℝ, 0 ≤ x → ‖(x : ℂ)‖ ^ 2 = y → (x : ℂ) = (Real.sqrt y : ℂ) := fun x y hx h => by
    rw [Complex.norm_real, Real.norm_of_nonneg hx] at h
    rw [← h, Real.sqrt_sq hx]
  refine key _ _ ?_ (norm_sq_primeHodgeCubicBirthVector hd p)
  refine mul_nonneg (by norm_num) (div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (Real.log_nonneg ?_)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  exact_mod_cast p.property.one_lt.le

theorem eight_sqrt_mul_sqrt_eq {μ ν x y : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hx : 0 < x) (hy : 0 < y) :
    8 * Real.sqrt (μ * x ^ 3) * Real.sqrt (ν * y ^ 3) =
      (x + y) ^ 3 * (Real.sqrt (μ * ν) * (2 * Real.sqrt (x * y) / (x + y)) ^ 3) := by
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ u ^ 2 = x := ⟨Real.sqrt x, Real.sqrt_pos.2 hx, Real.sq_sqrt hx.le⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, 0 < v ∧ v ^ 2 = y := ⟨Real.sqrt y, Real.sqrt_pos.2 hy, Real.sq_sqrt hy.le⟩
  rw [show μ * (u ^ 2) ^ 3 = μ * (u ^ 3) ^ 2 by ring, show ν * (v ^ 2) ^ 3 = ν * (v ^ 3) ^ 2 by ring,
    show u ^ 2 * v ^ 2 = (u * v) ^ 2 by ring, Real.sqrt_mul hμ, Real.sqrt_mul hν, Real.sqrt_mul hμ,
    Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)]
  have : u ^ 2 + v ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **(PCOB.7)** `A_d(p,q) = √(μ_d(p)μ_d(q)) c(λ_p, λ_q)³`. -/
theorem normalizedStokesPrimeKernel_eq_stokesEntry (hd : 0 < d) (p q : Nat.Primes) :
    normalizedStokesPrimeKernel d (p, q) = (stokesEntry d p q : ℂ) := by
  have h := primeHodgeCubicClock_normalizedStokesKernel hd p q
  have hp := primeClock_pos p
  have hq := primeClock_pos q
  have hs : ((Real.log (p : ℝ) + Real.log (q : ℝ) : ℝ) : ℂ) ^ (3 : ℕ) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.2 (by linarith))
  rw [primeHodgeCubicBirthVector_eq_sqrt hd, primeHodgeCubicBirthVector_eq_sqrt hd, Complex.star_def,
    Complex.conj_ofReal] at h
  rw [← mul_right_inj' hs, h, stokesEntry, apertureCoherence]
  rw [show (8 : ℂ) * ((Real.sqrt (primeFormationLaw d p * Real.log (p : ℝ) ^ 3) : ℝ) : ℂ) *
      ((Real.sqrt (primeFormationLaw d q * Real.log (q : ℝ) ^ 3) : ℝ) : ℂ) =
      ((8 * Real.sqrt (primeFormationLaw d p * Real.log (p : ℝ) ^ 3) *
        Real.sqrt (primeFormationLaw d q * Real.log (q : ℝ) ^ 3) : ℝ) : ℂ) by push_cast; ring,
    eight_sqrt_mul_sqrt_eq (primeFormationLaw_pos hd p).le (primeFormationLaw_pos hd q).le hp hq]
  push_cast
  ring

/-- **(PCOB.8)** Every entry of `A_d` is strictly positive. -/
theorem normalizedStokesPrimeKernel_pos (hd : 0 < d) (p q : Nat.Primes) :
    0 < normalizedStokesPrimeKernel d (p, q) := by
  rw [normalizedStokesPrimeKernel_eq_stokesEntry hd, Complex.zero_lt_real]
  exact stokesEntry_pos hd p q

/-- **(PCOB.8)** `A_d` is positive and trace class with `Tr A_d = ‖A_d‖₁ = 1`. -/
theorem traceNorm_normalizedStokesPrimeOperator (hd : 0 < d) :
    (normalizedStokesPrimeOperator hd).IsPositive ∧
      MemSchattenClass 1 (normalizedStokesPrimeOperator hd) ∧
      ContinuousLinearMap.opTrace (normalizedStokesPrimeOperator hd) = 1 ∧
      traceNorm ℓ²P (normalizedStokesPrimeOperator hd) = 1 := by
  have hpos := normalizedStokesPrimeOperator_isPositive' ⟨d, hd⟩
  have hS := normalizedStokesPrimeOperator_memSchattenClass_one' ⟨d, hd⟩
  have htr := opTrace_normalizedStokesPrimeOperator ⟨d, hd⟩
  refine ⟨hpos, hS, htr, ?_⟩
  rw [traceNorm_eq_re_opTrace_of_isPositive hS hpos, htr, Complex.one_re]

/-! ## The square of the Stokes operator -/

/-- The coherent transit `Σ_r μ_d(r) c(λ_p,λ_r)³ c(λ_r,λ_q)³` through the intermediate prime. -/
def stokesTransit (d : ℝ) (p q : Nat.Primes) : ℝ :=
  ∑' r : Nat.Primes, primeFormationLaw d r *
    apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 *
      apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3

theorem stokesTransit_term_nonneg (hd : 0 < d) (p q r : Nat.Primes) :
    0 ≤ primeFormationLaw d r * apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 *
      apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3 :=
  mul_nonneg (mul_nonneg (primeFormationLaw_pos hd r).le
    (pow_pos (apertureCoherence_pos (primeClock_pos p) (primeClock_pos r)) 3).le)
    (pow_pos (apertureCoherence_pos (primeClock_pos r) (primeClock_pos q)) 3).le

theorem summable_stokesTransit (hd : 0 < d) (p q : Nat.Primes) :
    Summable fun r : Nat.Primes => primeFormationLaw d r *
      apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 *
        apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3 := by
  refine Summable.of_nonneg_of_le (stokesTransit_term_nonneg hd p q) (fun r => ?_)
    (hasSum_primeFormationLaw hd).summable
  have h1 : apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 ≤ 1 :=
    pow_le_one₀ (apertureCoherence_pos (primeClock_pos p) (primeClock_pos r)).le
      (apertureCoherence_le_one (primeClock_pos p) (primeClock_pos r))
  have h2 : apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3 ≤ 1 :=
    pow_le_one₀ (apertureCoherence_pos (primeClock_pos r) (primeClock_pos q)).le
      (apertureCoherence_le_one (primeClock_pos r) (primeClock_pos q))
  have hμ := (primeFormationLaw_pos hd r).le
  have h2' := (pow_pos (apertureCoherence_pos (primeClock_pos r) (primeClock_pos q)) 3).le
  calc primeFormationLaw d r * apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 *
        apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3
      ≤ primeFormationLaw d r * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hμ) h2 h2' (by simpa using hμ)
    _ = primeFormationLaw d r := by ring

/-- **(PCOB.28)** `A_d²(p,q) = √(μ_d(p)μ_d(q)) Σ_r μ_d(r) c(λ_p,λ_r)³ c(λ_r,λ_q)³`. -/
theorem sq_normalizedStokesPrimeOperator_apply (hd : 0 < d) (p q : Nat.Primes) :
    ((normalizedStokesPrimeOperator hd ^ 2) (lp.single 2 q (1 : ℂ)) : Nat.Primes → ℂ) p =
      ((Real.sqrt (primeFormationLaw d p * primeFormationLaw d q) * stokesTransit d p q : ℝ) : ℂ) := by
  rw [sq]
  change (HilbertSchmidt.toOperator (normalizedStokesPrimeKernel_isHS hd)
    (HilbertSchmidt.toOperator (normalizedStokesPrimeKernel_isHS hd) (lp.single 2 q (1 : ℂ)))) p = _
  rw [HilbertSchmidt.toOperator_apply]
  simp_rw [HilbertSchmidt.toOperator_single, normalizedStokesPrimeKernel_eq_stokesEntry hd]
  have hterm : ∀ r : Nat.Primes, (stokesEntry d p r : ℂ) * (stokesEntry d r q : ℂ) =
      ((Real.sqrt (primeFormationLaw d p * primeFormationLaw d q) *
        (primeFormationLaw d r * apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 *
          apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3) : ℝ) : ℂ) := fun r => by
    rw [← Complex.ofReal_mul]
    congr 1
    have hp := (primeFormationLaw_pos hd p).le
    have hq := (primeFormationLaw_pos hd q).le
    have hr := (primeFormationLaw_pos hd r).le
    rw [stokesEntry, stokesEntry, Real.sqrt_mul hp, Real.sqrt_mul hr, Real.sqrt_mul hp]
    linear_combination (Real.sqrt (primeFormationLaw d p) * Real.sqrt (primeFormationLaw d q) *
      apertureCoherence (Real.log (p : ℝ)) (Real.log (r : ℝ)) ^ 3 *
        apertureCoherence (Real.log (r : ℝ)) (Real.log (q : ℝ)) ^ 3) * Real.mul_self_sqrt hr
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, tsum_mul_left, stokesTransit]

/-! ## Logarithmic blocks -/

/-- The primes of the logarithmic window `a < d log p ≤ b`. -/
def windowFinset (d a b : ℝ) : Finset Nat.Primes :=
  (Finset.Ioc ⌊Real.exp (a / d)⌋₊ ⌊Real.exp (b / d)⌋₊).preimage ((↑) : Nat.Primes → ℕ)
    Nat.Primes.coe_nat_injective.injOn

theorem mem_windowFinset {a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (p : Nat.Primes) :
    p ∈ windowFinset d a b ↔ a < d * Real.log (p : ℝ) ∧ d * Real.log (p : ℝ) ≤ b := by
  rw [windowFinset, Finset.mem_preimage, ← mem_window_iff hd ha]

theorem primeFormationWindowMass_eq_sum {a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) :
    primeFormationWindowMass d a b = ∑ p ∈ windowFinset d a b, primeFormationLaw d p := by
  have h0 : ∀ p ∉ windowFinset d a b, Set.indicator
      {p : Nat.Primes | a < d * Real.log (p : ℝ) ∧ d * Real.log (p : ℝ) ≤ b}
      (primeFormationLaw d) p = 0 := fun p hp =>
    Set.indicator_of_notMem (show p ∉ {p : Nat.Primes | a < d * Real.log (p : ℝ) ∧
      d * Real.log (p : ℝ) ≤ b} from fun h => hp ((mem_windowFinset hd ha p).2 h)) _
  have h1 : ∀ p ∈ windowFinset d a b, Set.indicator
      {p : Nat.Primes | a < d * Real.log (p : ℝ) ∧ d * Real.log (p : ℝ) ≤ b}
      (primeFormationLaw d) p = primeFormationLaw d p := fun p hp =>
    Set.indicator_of_mem (show p ∈ {p : Nat.Primes | a < d * Real.log (p : ℝ) ∧
      d * Real.log (p : ℝ) ≤ b} from (mem_windowFinset hd ha p).1 hp) _
  rw [primeFormationWindowMass, tsum_eq_sum h0]
  exact Finset.sum_congr rfl h1

/-- Every logarithmic block `(a, b]`, `0 < a < b`, eventually carries at least half of its
limiting mass `e^{-2a} - e^{-2b}`. -/
theorem eventually_half_le_windowMass {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ d in 𝓝[>] (0 : ℝ),
      (Real.exp (-2 * a) - Real.exp (-2 * b)) / 2 < primeFormationWindowMass d a b := by
  have h := tendsto_primeFormationWindowMass ha hab.le
  rw [two_mul_integral_exp_neg_two] at h
  have hpos : 0 < Real.exp (-2 * a) - Real.exp (-2 * b) :=
    sub_pos.2 (Real.exp_lt_exp.2 (by linarith))
  exact (tendsto_order.1 h).1 _ (half_lt_self hpos)

/-! ## The commutator with the prime clock -/

/-- The matrix of `[L, A_d²]` in the prime basis, `L e_p = λ_p e_p`:
`⟨e_p, [L, A_d²] e_q⟩ = (λ_p - λ_q) A_d²(p,q)`. -/
def squareCommutatorEntry (hd : 0 < d) (pq : Nat.Primes × Nat.Primes) : ℂ :=
  ((Real.log (pq.1 : ℝ) - Real.log (pq.2 : ℝ) : ℝ) : ℂ) *
    ((normalizedStokesPrimeOperator hd ^ 2) (lp.single 2 pq.2 (1 : ℂ)) : Nat.Primes → ℂ) pq.1

theorem norm_sq_squareCommutatorEntry (hd : 0 < d) (p q : Nat.Primes) :
    ‖squareCommutatorEntry hd (p, q)‖ ^ 2 =
      (Real.log (p : ℝ) - Real.log (q : ℝ)) ^ 2 *
        (primeFormationLaw d p * primeFormationLaw d q) * stokesTransit d p q ^ 2 := by
  rw [squareCommutatorEntry, sq_normalizedStokesPrimeOperator_apply, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, mul_pow,
    Real.sq_sqrt (mul_pos (primeFormationLaw_pos hd p) (primeFormationLaw_pos hd q)).le]
  ring

/-- On the blocks `1 < dλ_p ≤ 2`, `4 < dλ_q ≤ 5`, each commutator entry dominates
`(4/d²) 5^{-12} μ(2,3]² μ_d(p) μ_d(q)`. -/
theorem norm_sq_squareCommutatorEntry_ge (hd : 0 < d) {p q : Nat.Primes}
    (hp : p ∈ windowFinset d 1 2) (hq : q ∈ windowFinset d 4 5) :
    4 / d ^ 2 * (1 / 5) ^ 12 * primeFormationWindowMass d 2 3 ^ 2 *
        (primeFormationLaw d p * primeFormationLaw d q) ≤ ‖squareCommutatorEntry hd (p, q)‖ ^ 2 := by
  rw [mem_windowFinset hd zero_le_one] at hp
  rw [mem_windowFinset hd (by norm_num)] at hq
  rw [norm_sq_squareCommutatorEntry]
  have hμ := mul_pos (primeFormationLaw_pos hd p) (primeFormationLaw_pos hd q)
  -- the transit through the middle block
  have htransit : (1 / 5) ^ 6 * primeFormationWindowMass d 2 3 ≤ stokesTransit d p q := by
    rw [primeFormationWindowMass_eq_sum hd (by norm_num), Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun r hr => ?_)
      ((summable_stokesTransit hd p q).sum_le_tsum _ fun r _ => stokesTransit_term_nonneg hd p q r)
    rw [mem_windowFinset hd (by norm_num)] at hr
    have h1 := apertureCoherence_ge (s := Real.log (p : ℝ)) (t := Real.log (r : ℝ)) hd hp.1
      (by linarith [hp.2]) (by linarith [hr.1]) (by linarith [hr.2])
    have h2 := apertureCoherence_ge (s := Real.log (r : ℝ)) (t := Real.log (q : ℝ)) hd
      (by linarith [hr.1]) (by linarith [hr.2]) (by linarith [hq.1]) hq.2
    have hμr := (primeFormationLaw_pos hd r).le
    calc (1 / 5) ^ 6 * primeFormationLaw d r = primeFormationLaw d r * (1 / 5) ^ 3 * (1 / 5) ^ 3 := by
          ring
      _ ≤ _ := by gcongr
  have hm0 : 0 ≤ primeFormationWindowMass d 2 3 := by
    rw [primeFormationWindowMass_eq_sum hd (by norm_num)]
    exact Finset.sum_nonneg fun r _ => (primeFormationLaw_pos hd r).le
  have hgap : 2 / d < Real.log (q : ℝ) - Real.log (p : ℝ) := by
    rw [div_lt_iff₀ hd]
    linarith [hp.2, hq.1]
  have hgap2 : 4 / d ^ 2 ≤ (Real.log (p : ℝ) - Real.log (q : ℝ)) ^ 2 := by
    have h0 : 0 < 2 / d := by positivity
    have := mul_self_le_mul_self h0.le hgap.le
    calc 4 / d ^ 2 = 2 / d * (2 / d) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have ht2 : ((1 / 5) ^ 6 * primeFormationWindowMass d 2 3) ^ 2 ≤ stokesTransit d p q ^ 2 :=
    pow_le_pow_left₀ (by positivity) htransit 2
  calc 4 / d ^ 2 * (1 / 5) ^ 12 * primeFormationWindowMass d 2 3 ^ 2 *
        (primeFormationLaw d p * primeFormationLaw d q)
      = 4 / d ^ 2 * (primeFormationLaw d p * primeFormationLaw d q) *
          ((1 / 5) ^ 6 * primeFormationWindowMass d 2 3) ^ 2 := by ring
    _ ≤ (Real.log (p : ℝ) - Real.log (q : ℝ)) ^ 2 * (primeFormationLaw d p * primeFormationLaw d q) *
          stokesTransit d p q ^ 2 := by gcongr

/-- The block constant `c₀ = 4·5^{-12} (ℓ₂₃/2)² (ℓ₁₂/2) (ℓ₄₅/2)`, `ℓ_{ab} = e^{-2a} - e^{-2b}`. -/
def squareCommutatorConstant : ℝ :=
  4 * (1 / 5) ^ 12 * ((Real.exp (-2 * 2) - Real.exp (-2 * 3)) / 2) ^ 2 *
    ((Real.exp (-2 * 1) - Real.exp (-2 * 2)) / 2) * ((Real.exp (-2 * 4) - Real.exp (-2 * 5)) / 2)

theorem squareCommutatorConstant_pos : 0 < squareCommutatorConstant := by
  have h : ∀ a b : ℝ, a < b → 0 < (Real.exp (-2 * a) - Real.exp (-2 * b)) / 2 := fun a b hab =>
    half_pos (sub_pos.2 (Real.exp_lt_exp.2 (by linarith)))
  unfold squareCommutatorConstant
  have := h 2 3 (by norm_num)
  have := h 1 2 (by norm_num)
  have := h 4 5 (by norm_num)
  positivity

/-- **Finite block bound.**  For all small apertures the commutator mass on the blocks
`(1,2] × (4,5]` is at least `c₀/d²`. -/
theorem exists_squareCommutator_block_bound :
    ∃ d₀ > 0, ∀ d (hd : 0 < d), d < d₀ →
      squareCommutatorConstant / d ^ 2 ≤
        ∑ pq ∈ windowFinset d 1 2 ×ˢ windowFinset d 4 5, ‖squareCommutatorEntry hd pq‖ ^ 2 := by
  have hev := (eventually_half_le_windowMass one_pos (by norm_num : (1 : ℝ) < 2)).and
    ((eventually_half_le_windowMass (by norm_num) (by norm_num : (2 : ℝ) < 3)).and
      (eventually_half_le_windowMass (by norm_num) (by norm_num : (4 : ℝ) < 5)))
  obtain ⟨d₀, hd₀, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨d₀, hd₀, fun d hd hdd => ?_⟩
  obtain ⟨hI, hK, hJ⟩ := hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hd]; exact hdd) hd
  rw [Finset.sum_product]
  have hbound : ∀ p ∈ windowFinset d 1 2, ∀ q ∈ windowFinset d 4 5,
      4 / d ^ 2 * (1 / 5) ^ 12 * primeFormationWindowMass d 2 3 ^ 2 *
        (primeFormationLaw d p * primeFormationLaw d q) ≤ ‖squareCommutatorEntry hd (p, q)‖ ^ 2 :=
    fun p hp q hq => norm_sq_squareCommutatorEntry_ge hd hp hq
  refine le_trans ?_ (Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hbound p hp q hq)
  have hℓ : ∀ a b : ℝ, a < b → 0 ≤ (Real.exp (-2 * a) - Real.exp (-2 * b)) / 2 := fun a b hab =>
    (half_pos (sub_pos.2 (Real.exp_lt_exp.2 (by linarith)))).le
  have hK0 := hℓ 2 3 (by norm_num)
  have hI0 := hℓ 1 2 (by norm_num)
  have hJ0 := hℓ 4 5 (by norm_num)
  have key : squareCommutatorConstant / d ^ 2 ≤
      4 / d ^ 2 * (1 / 5) ^ 12 * primeFormationWindowMass d 2 3 ^ 2 *
        (primeFormationWindowMass d 1 2 * primeFormationWindowMass d 4 5) := by
    have e : squareCommutatorConstant / d ^ 2 =
        4 / d ^ 2 * (1 / 5) ^ 12 * ((Real.exp (-2 * 2) - Real.exp (-2 * 3)) / 2) ^ 2 *
          (((Real.exp (-2 * 1) - Real.exp (-2 * 2)) / 2) *
            ((Real.exp (-2 * 4) - Real.exp (-2 * 5)) / 2)) := by
      unfold squareCommutatorConstant
      ring
    rw [e]
    have hsq := pow_le_pow_left₀ hK0 hK.le 2
    have hprod := mul_le_mul hI.le hJ.le hJ0 (hI0.trans hI.le)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsq (by positivity)) hprod
      (mul_nonneg hI0 hJ0) (by positivity)
  refine key.trans (le_of_eq ?_)
  rw [primeFormationWindowMass_eq_sum hd zero_le_one,
    primeFormationWindowMass_eq_sum hd (by norm_num : (0 : ℝ) ≤ 4), Finset.sum_mul_sum,
    Finset.mul_sum]
  simp_rw [Finset.mul_sum]

/-- **(PCOB.29)** The Hilbert–Schmidt mass of `[L, A_d²]` is at least `c₀/d²` for all small
apertures: `Σ_{p,q} |⟨e_p, [L, A_d²] e_q⟩|² ≥ c₀/d²` in `[0, ∞]`. -/
theorem squareCommutator_hsMass_ge :
    ∃ c₀ > 0, ∃ d₀ > 0, ∀ d (hd : 0 < d), d < d₀ →
      ENNReal.ofReal (c₀ / d ^ 2) ≤ ∑' pq, ENNReal.ofReal (‖squareCommutatorEntry hd pq‖ ^ 2) := by
  obtain ⟨d₀, hd₀, h⟩ := exists_squareCommutator_block_bound
  refine ⟨squareCommutatorConstant, squareCommutatorConstant_pos, d₀, hd₀, fun d hd hdd => ?_⟩
  calc ENNReal.ofReal (squareCommutatorConstant / d ^ 2)
      ≤ ENNReal.ofReal (∑ pq ∈ windowFinset d 1 2 ×ˢ windowFinset d 4 5,
          ‖squareCommutatorEntry hd pq‖ ^ 2) := ENNReal.ofReal_le_ofReal (h d hd hdd)
    _ = ∑ pq ∈ windowFinset d 1 2 ×ˢ windowFinset d 4 5,
          ENNReal.ofReal (‖squareCommutatorEntry hd pq‖ ^ 2) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _
    _ ≤ _ := ENNReal.sum_le_tsum _

/-! ## The joint defect -/

/-- On a fixed history mode, `𝖳_d² = Φ² ⊗ A_d²`: `𝖳_d²((n,p),(n,q)) = w_n² A_d²(p,q)`. -/
theorem sq_primeHodgeHistoryDefectOperator_apply (hd : 0 < d) (n : ℕ) (p q : Nat.Primes) :
    ((primeHodgeHistoryDefectOperator hd ^ 2) (lp.single 2 (n, q) (1 : ℂ)) :
        PrimeHodgeHistoryIndex → ℂ) (n, p) =
      (PrimeHodgeHistory.w n : ℂ) ^ 2 *
        ((normalizedStokesPrimeOperator hd ^ 2) (lp.single 2 q (1 : ℂ)) : Nat.Primes → ℂ) p := by
  rw [sq (primeHodgeHistoryDefectOperator hd), sq (normalizedStokesPrimeOperator hd)]
  change (HilbertSchmidt.toOperator (primeHodgeHistoryDefectKernel_isHS hd)
      (HilbertSchmidt.toOperator (primeHodgeHistoryDefectKernel_isHS hd)
        (lp.single 2 (n, q) (1 : ℂ)))) (n, p) =
    (PrimeHodgeHistory.w n : ℂ) ^ 2 * (HilbertSchmidt.toOperator (normalizedStokesPrimeKernel_isHS hd)
      (HilbertSchmidt.toOperator (normalizedStokesPrimeKernel_isHS hd) (lp.single 2 q (1 : ℂ)))) p
  rw [HilbertSchmidt.toOperator_apply, HilbertSchmidt.toOperator_apply]
  simp_rw [HilbertSchmidt.toOperator_single]
  rw [← tsum_mul_left]
  have htr : ∑' r : Nat.Primes, primeHodgeHistoryDefectKernel d ((n, p), (n, r)) *
      primeHodgeHistoryDefectKernel d ((n, r), (n, q)) =
      ∑' c : PrimeHodgeHistoryIndex, primeHodgeHistoryDefectKernel d ((n, p), c) *
        primeHodgeHistoryDefectKernel d (c, (n, q)) :=
    Function.Injective.tsum_eq (Prod.mk_right_injective n)
      (f := fun c : PrimeHodgeHistoryIndex => primeHodgeHistoryDefectKernel d ((n, p), c) *
        primeHodgeHistoryDefectKernel d (c, (n, q))) fun c hc => by
      by_contra h
      apply hc
      have hc1 : n ≠ c.1 := fun h1 => h ⟨c.2, Prod.ext h1 rfl⟩
      simp only [primeHodgeHistoryDefectKernel, if_neg hc1, zero_mul]
  rw [← htr]
  refine tsum_congr fun r => ?_
  simp only [primeHodgeHistoryDefectKernel, if_true]
  ring

/-- The matrix of `(I ⊗ L)𝖳_d² - 𝖳_d²(I ⊗ L)` in the history–prime basis. -/
def jointSquareCommutatorEntry (hd : 0 < d)
    (ab : PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex) : ℂ :=
  ((Real.log (ab.1.2 : ℝ) - Real.log (ab.2.2 : ℝ) : ℝ) : ℂ) *
    ((primeHodgeHistoryDefectOperator hd ^ 2) (lp.single 2 ab.2 (1 : ℂ)) :
      PrimeHodgeHistoryIndex → ℂ) ab.1

theorem jointSquareCommutatorEntry_same (hd : 0 < d) (n : ℕ) (p q : Nat.Primes) :
    jointSquareCommutatorEntry hd ((n, p), (n, q)) =
      (PrimeHodgeHistory.w n : ℂ) ^ 2 * squareCommutatorEntry hd (p, q) := by
  rw [jointSquareCommutatorEntry, squareCommutatorEntry, sq_primeHodgeHistoryDefectOperator_apply]
  ring

/-- **(PCOB.30)** The Hilbert–Schmidt mass of `(I ⊗ L)𝖳_d² - 𝖳_d²(I ⊗ L)` is unbounded as
`d → 0+`: it exceeds every real bound for all sufficiently small apertures. -/
theorem jointSquareCommutator_hsMass_unbounded (M : ℝ) :
    ∃ d₁ > 0, ∀ d (hd : 0 < d), d < d₁ →
      ENNReal.ofReal M ≤ ∑' ab, ENNReal.ofReal (‖jointSquareCommutatorEntry hd ab‖ ^ 2) := by
  obtain ⟨d₀, hd₀, h⟩ := exists_squareCommutator_block_bound
  have hw := PrimeHodgeHistory.w_pos 0
  set c := PrimeHodgeHistory.w 0 ^ 4 * squareCommutatorConstant with hc_def
  have hc : 0 < c := mul_pos (pow_pos hw 4) squareCommutatorConstant_pos
  refine ⟨min d₀ (Real.sqrt (c / (|M| + 1))),
    lt_min hd₀ (Real.sqrt_pos.2 (by positivity)), fun d hd hdd => ?_⟩
  have hd0 : d < d₀ := lt_of_lt_of_le hdd (min_le_left _ _)
  have hd2 : d ^ 2 < c / (|M| + 1) :=
    (Real.lt_sqrt hd.le).1 (lt_of_lt_of_le hdd (min_le_right _ _))
  have hM : M ≤ c / d ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hd2
    nlinarith [le_abs_self M, abs_nonneg M, sq_nonneg d]
  let emb : Nat.Primes × Nat.Primes ↪ PrimeHodgeHistoryIndex × PrimeHodgeHistoryIndex :=
    ⟨fun pq => ((0, pq.1), (0, pq.2)), fun x y hxy => by
      simp only [Prod.mk.injEq] at hxy
      exact Prod.ext hxy.1.2 hxy.2.2⟩
  calc ENNReal.ofReal M ≤ ENNReal.ofReal (c / d ^ 2) := ENNReal.ofReal_le_ofReal hM
    _ ≤ ENNReal.ofReal (∑ pq ∈ windowFinset d 1 2 ×ˢ windowFinset d 4 5,
          PrimeHodgeHistory.w 0 ^ 4 * ‖squareCommutatorEntry hd pq‖ ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        calc c / d ^ 2 = PrimeHodgeHistory.w 0 ^ 4 * (squareCommutatorConstant / d ^ 2) := by
              rw [hc_def]
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (h d hd hd0) (by positivity)
    _ = ∑ pq ∈ windowFinset d 1 2 ×ˢ windowFinset d 4 5,
          ENNReal.ofReal (‖jointSquareCommutatorEntry hd (emb pq)‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
        refine Finset.sum_congr rfl fun pq _ => ?_
        obtain ⟨p, q⟩ := pq
        change _ = ENNReal.ofReal (‖jointSquareCommutatorEntry hd ((0, p), (0, q))‖ ^ 2)
        rw [jointSquareCommutatorEntry_same, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hw.le]
        ring_nf
    _ = ∑ ab ∈ (windowFinset d 1 2 ×ˢ windowFinset d 4 5).map emb,
          ENNReal.ofReal (‖jointSquareCommutatorEntry hd ab‖ ^ 2) :=
        (Finset.sum_map (windowFinset d 1 2 ×ˢ windowFinset d 4 5) emb
          fun ab => ENNReal.ofReal (‖jointSquareCommutatorEntry hd ab‖ ^ 2)).symm
    _ ≤ _ := ENNReal.sum_le_tsum _

end GaloisForLFunctions.HTGeometry
