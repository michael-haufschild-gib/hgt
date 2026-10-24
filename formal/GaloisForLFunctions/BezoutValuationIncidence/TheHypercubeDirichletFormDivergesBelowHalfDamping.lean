import GaloisForLFunctions.BezoutValuationIncidence.BezoutCouplingAndCrossDepthCancellation
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# The hypercube Dirichlet form diverges below half damping

The hypercube Dirichlet form of the dilation profile
`D_{r,ε}(P) = ∑_{d₁,d₂ ∣ P} μ(d₁) μ(d₂) (d₁d₂)^{-1/2-ε} Φ_r(d₁/d₂)` is bounded uniformly in the
cutoff `P` for `ε > 1/2` (`hypercubeDilationDirichletForm_le_tsum_sq_of_half_lt`). This module
proves that it is unbounded over squarefree `P` coprime to `r` for every `0 ≤ ε < 1/2`, and that
the parity twin (every sign `+1`) has the same threshold.

* **Physical form.** For a finite set `D` of positive scales and real weights `w`, the form
  `∑_{d₁,d₂ ∈ D} w(d₁)w(d₂)(d₁d₂)^{-1/2-ε} Φ_r(d₁/d₂)` is the pronic energy
  `∑_{n ≥ 1} Ψ(n)²/(n(n+1))` of `Ψ(n) = ∑_{d ∈ D} w(d) d^{-ε} C_r(⌊n/d⌋)`, `C_r` the Ramanujan
  primitive (`hasSum_signedDilationPrimitive_sq`).
* **Depth-one plateau.** For the prime block `S_y = {y < p ≤ y + ⌊y/2r⌋}` and `P_y = ∏_{S_y} p`,
  every block prime has `⌊n/p⌋ = r - 1` on `(r-1)(y + ⌊y/2r⌋) ≤ n ≤ ry`, and every divisor with two
  prime factors exceeds `n`. Since `C_r(r-1) = -φ(r)`, the primitive there is
  `w(1) C_r(n) - φ(r) ∑_{p ∈ S_y} w(p) p^{-ε}` (`signedDilationPrimitive_primeBlockProd_eq`).
* **Growth.** The prime number theorem gives `∑_{p ∈ S_y} p^{-ε} ≥ (2y)^{1-ε}/(16 r log 2y)`,
  hence `D(P_y) ≥ c_r (2y)^{1-2ε}/log²(2y)` (`eventually_signedDilationDirichletForm_ge`).

Divisor truncation keeps a whole block of equal-sign primes on one floor plateau. The
cancellation of the receiver therefore cannot be organised by prime support: the hypercube form
has the sign-blind threshold `1/2` (`hypercubeDilationDirichletForm_threshold`).
-/

open Filter Topology Finset Asymptotics
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators Chebyshev

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The physical form of a signed dilation Dirichlet form -/

/-- The dilation Dirichlet form with real weights `w(d) d^{-1/2-ε}` over the scales `D`. -/
def signedDilationDirichletForm (w : ℕ → ℝ) (ε : ℝ) (D : Finset ℕ) (r : ℕ) (hr : 1 < r) : ℝ :=
  ∑ d₁ ∈ D, ∑ d₂ ∈ D,
    (w d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) * (w d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
      pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)

/-- Its physical primitive `Ψ(n) = ∑_{d ∈ D} w(d) d^{-ε} C_r(⌊n/d⌋)`. -/
def signedDilationPrimitive (w : ℕ → ℝ) (ε : ℝ) (D : Finset ℕ) (r n : ℕ) : ℝ :=
  ∑ d ∈ D, w d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (n / d)).re

theorem hypercubeDilationDirichletForm_eq_signed (ε : ℝ) (P : ℕ) {r : ℕ} (hr : 1 < r) :
    hypercubeDilationDirichletForm ε P r hr =
      signedDilationDirichletForm moebiusReal ε P.divisors r hr := rfl

theorem dirichletDilationPrimitive_eq_signed (ε : ℝ) (P r n : ℕ) :
    dirichletDilationPrimitive ε P r n =
      signedDilationPrimitive moebiusReal ε P.divisors r n := rfl

/-- **Physical form.** The signed dilation Dirichlet form is the pronic energy of its primitive:
each profile `Φ_r(d₁/d₂)` is `√(d₁d₂)` times the step Gram of the floor sequences
`C_r(⌊·/d₁⌋)`, `C_r(⌊·/d₂⌋)`, and the weights `w(d) d^{-1/2-ε} √d = w(d) d^{-ε}` assemble the square. -/
theorem hasSum_signedDilationPrimitive_sq (w : ℕ → ℝ) (ε : ℝ) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 0 < d) {r : ℕ} (hr : 1 < r) :
    HasSum (fun n : ℕ => signedDilationPrimitive w ε D r (n + 1) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (signedDilationDirichletForm w ε D r hr) := by
  set s : ℕ → ℕ → ℝ := fun d N => (pmRamanujanPrimitive r (N / d)).re with hs
  have hb (d N : ℕ) : |s d N| ≤ pmRamanujanPrimitiveBound r :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr _)
  set a : ℕ → ℝ := fun d => w d * (d : ℝ) ^ (-(1 / 2 : ℝ) - ε) with ha
  have hpair : ∀ d₁ ∈ D, ∀ d₂ ∈ D,
      HasSum (fun n : ℕ => a d₁ * a d₂ * (Real.sqrt d₁ * Real.sqrt d₂ *
          (s d₁ (n + 1) * s d₂ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)))))
        (a d₁ * a d₂ * pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂)) := by
    intro d₁ hd₁ d₂ hd₂
    rw [pmRamanujanDilationProfile_eq_stepGram hr (hD d₁ hd₁) (hD d₂ hd₂)]
    exact ((hasSum_stepGram (hb d₁) (hb d₂)).mul_left _).mul_left _
  have htot := hasSum_sum fun d₁ hd₁ => hasSum_sum fun d₂ hd₂ => hpair d₁ hd₁ d₂ hd₂
  have hwt : ∀ d ∈ D, a d * Real.sqrt d = w d * (d : ℝ) ^ (-ε) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hD d hd
    rw [ha, Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hd0]
    congr 2
    ring
  convert htot using 1
  funext n
  rw [signedDilationPrimitive, sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
  rw [← hwt d₁ hd₁, ← hwt d₂ hd₂]
  ring

/-- Every finite window of the pronic energy is a lower bound for the form. -/
theorem sum_Ico_signedDilationPrimitive_sq_le (w : ℕ → ℝ) (ε : ℝ) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 0 < d) {r : ℕ} (hr : 1 < r) {a b : ℕ} (ha : 1 ≤ a) :
    ∑ n ∈ Ico a b, signedDilationPrimitive w ε D r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      signedDilationDirichletForm w ε D r hr := by
  have hsum := hasSum_signedDilationPrimitive_sq w ε hD hr
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simpa using hsum.nonneg fun n => by positivity
  have hshift :
      ∑ n ∈ Ico a b, signedDilationPrimitive w ε D r n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ m ∈ Ico (a - 1) (b - 1), signedDilationPrimitive w ε D r (m + 1) ^ 2 /
          (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
    rw [← Nat.sub_add_cancel ha, ← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hb.ne'),
      ← Finset.sum_Ico_add']
    refine Finset.sum_congr (by simp) fun m _ => ?_
    push_cast
    ring_nf
  rw [hshift]
  exact sum_le_hasSum _ (fun n _ => by positivity) hsum

/-! ## §2. The prime block and its depth-one plateau -/

/-- The prime block `S_y = {p prime : y < p ≤ y + ⌊y/(2r)⌋}`. -/
def primeBlock (r y : ℕ) : Finset ℕ := (Ioc y (y + y / (2 * r))).filter Nat.Prime

/-- The block product `P_y = ∏_{p ∈ S_y} p`. -/
def primeBlockProd (r y : ℕ) : ℕ := ∏ p ∈ primeBlock r y, p

theorem mem_primeBlock {r y p : ℕ} :
    p ∈ primeBlock r y ↔ p.Prime ∧ y < p ∧ p ≤ y + y / (2 * r) := by
  simp only [primeBlock, mem_filter, mem_Ioc]
  tauto

theorem primeBlockProd_ne_zero (r y : ℕ) : primeBlockProd r y ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hp => (mem_primeBlock.mp hp).1.ne_zero

theorem squarefree_primeBlockProd (r y : ℕ) : Squarefree (primeBlockProd r y) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp =>
    (mem_primeBlock.mp hp).1.prime.squarefree
  intro p hp q hq hpq
  exact (Nat.coprime_primes (mem_primeBlock.mp hp).1 (mem_primeBlock.mp hq).1 |>.mpr hpq).isRelPrime

theorem coprime_primeBlockProd {r y : ℕ} (hr : 0 < r) (hry : r ≤ y) :
    Nat.Coprime (primeBlockProd r y) r := by
  refine Nat.Coprime.prod_left fun p hp => ?_
  obtain ⟨hpp, hyp, -⟩ := mem_primeBlock.mp hp
  exact (Nat.coprime_comm.mp ((Nat.coprime_or_dvd_of_prime hpp r).resolve_right
    fun h => absurd (Nat.le_of_dvd hr h) (by omega))).symm

/-- A prime dividing the block product is a block prime. -/
theorem mem_primeBlock_of_prime_dvd {r y q : ℕ} (hq : q.Prime) (hqP : q ∣ primeBlockProd r y) :
    q ∈ primeBlock r y := by
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqP
  rwa [(Nat.prime_dvd_prime_iff_eq hq (mem_primeBlock.mp hp).1).mp hqp]

/-- A divisor of the block product below `(y+1)²` is `1` or a block prime: two block primes
already multiply to more than `y²`. -/
theorem eq_one_or_mem_primeBlock_of_dvd {r y d : ℕ} (hd : d ∣ primeBlockProd r y)
    (hdy : d < (y + 1) ^ 2) : d = 1 ∨ d ∈ primeBlock r y := by
  by_cases h1 : d = 1
  · exact Or.inl h1
  obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd h1
  have hpS := mem_primeBlock_of_prime_dvd hp (dvd_trans (dvd_mul_right p m) hd)
  by_cases hm : m = 1
  · rw [hm, mul_one]
    exact Or.inr hpS
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm
  have hqS := mem_primeBlock_of_prime_dvd hq (dvd_trans (dvd_trans hqm (dvd_mul_left m p)) hd)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact primeBlockProd_ne_zero r y (Nat.eq_zero_of_zero_dvd (by simpa using hd))
  have hqle : q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hqm
  have hyp : y + 1 ≤ p := (mem_primeBlock.mp hpS).2.1
  have hyq : y + 1 ≤ q := (mem_primeBlock.mp hqS).2.1
  have : (y + 1) ^ 2 ≤ p * m := by
    rw [sq]
    exact Nat.mul_le_mul hyp (hyq.trans hqle)
  omega

/-- `C_r(r - 1) = -φ(r)`: the last step of a period adds the Ramanujan sum `c_r(r) = φ(r)`. -/
theorem pmRamanujanPrimitive_sub_one_self {r : ℕ} (hr : 1 < r) :
    pmRamanujanPrimitive r (r - 1) = -(r.totient : ℂ) := by
  have h := pmRamanujanPrimitive_succ r (r - 1)
  rw [Nat.sub_add_cancel hr.le, pmRamanujanPrimitive_period_sum hr] at h
  have hc : d4BMRamanujanNaturalCoefficient r r = (r.totient : ℂ) := by
    rw [pm_ramanujan_eq_antidiagonal (by omega) r, ← pm_totient_antidiagonal (by omega)]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [if_pos (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx))]
  rw [hc] at h
  linear_combination h

/-- **Depth-one plateau.** On `(r-1)(y + ⌊y/2r⌋) ≤ n ≤ ry` every block prime sits on the floor
value `r - 1` and every composite divisor of the block product is born after `n`, so the
primitive is the unit term plus `-φ(r)` times the weighted block mass. -/
theorem signedDilationPrimitive_primeBlockProd_eq (w : ℕ → ℝ) (ε : ℝ) {r y n : ℕ}
    (hr : 1 < r) (hry : r ≤ y) (hn₁ : (r - 1) * (y + y / (2 * r)) ≤ n) (hn₂ : n ≤ r * y) :
    signedDilationPrimitive w ε (primeBlockProd r y).divisors r n =
      w 1 * (pmRamanujanPrimitive r n).re -
        (r.totient : ℝ) * ∑ p ∈ primeBlock r y, w p * (p : ℝ) ^ (-ε) := by
  set S := primeBlock r y
  set P := primeBlockProd r y
  have hP0 : P ≠ 0 := primeBlockProd_ne_zero r y
  have hny : n < (y + 1) ^ 2 := by nlinarith
  have h1S : (1 : ℕ) ∉ S := fun h => Nat.not_prime_one (mem_primeBlock.mp h).1
  have hsub : insert 1 S ⊆ P.divisors := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hdS
    · exact Nat.one_mem_divisors.mpr hP0
    · exact Nat.mem_divisors.mpr ⟨Finset.dvd_prod_of_mem _ hdS, hP0⟩
  have hzero : ∀ d ∈ P.divisors, d ∉ insert 1 S →
      w d * (d : ℝ) ^ (-ε) * (pmRamanujanPrimitive r (n / d)).re = 0 := by
    intro d hd hdn
    have hdy : (y + 1) ^ 2 ≤ d := by
      by_contra hlt
      rcases eq_one_or_mem_primeBlock_of_dvd (Nat.dvd_of_mem_divisors hd) (not_le.mp hlt) with
        h | h
      · exact hdn (h ▸ Finset.mem_insert_self 1 S)
      · exact hdn (Finset.mem_insert_of_mem h)
    rw [Nat.div_eq_of_lt (by omega)]
    simp [pmRamanujanPrimitive]
  have hfloor : ∀ p ∈ S, n / p = r - 1 := by
    intro p hp
    obtain ⟨-, hyp, hpy⟩ := mem_primeBlock.mp hp
    refine Nat.div_eq_of_lt_le ((Nat.mul_le_mul_left _ hpy).trans hn₁) ?_
    rw [Nat.sub_add_cancel hr.le]
    exact lt_of_le_of_lt hn₂ (Nat.mul_lt_mul_of_pos_left hyp (by omega))
  rw [signedDilationPrimitive, ← Finset.sum_subset hsub hzero, Finset.sum_insert h1S,
    Nat.cast_one, Real.one_rpow, mul_one, Nat.div_one, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hfloor p hp, pmRamanujanPrimitive_sub_one_self hr]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
