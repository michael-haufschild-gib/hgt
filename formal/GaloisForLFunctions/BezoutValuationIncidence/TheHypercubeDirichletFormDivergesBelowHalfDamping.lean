import GaloisForLFunctions.BezoutValuationIncidence.BezoutCouplingAndCrossDepthCancellation
import GaloisForLFunctions.RHTower.ThetaPrimeScheduleSpectralObservation

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
`C_r(⌊·/d₁⌋)`, `C_r(⌊·/d₂⌋)`, and the weights `w(d) d^{-1/2-ε} √d = w(d) d^{-ε}` assemble the
square. -/
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
  · funext n
    rw [signedDilationPrimitive, sq, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
    rw [← hwt d₁ hd₁, ← hwt d₂ hd₂]
    ring
  · rfl

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
  Finset.prod_ne_zero_iff.mpr fun _ hp => (mem_primeBlock.mp hp).1.ne_zero

theorem squarefree_primeBlockProd (r y : ℕ) : Squarefree (primeBlockProd r y) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp =>
    (mem_primeBlock.mp hp).1.prime.squarefree
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (mem_primeBlock.mp hp).1 (mem_primeBlock.mp hq).1).mpr hpq)

theorem coprime_primeBlockProd {r y : ℕ} (hr : 0 < r) (hry : r ≤ y) :
    Nat.Coprime (primeBlockProd r y) r := by
  refine Nat.Coprime.prod_left fun p hp => ?_
  obtain ⟨hpp, hyp, -⟩ := mem_primeBlock.mp hp
  exact (Nat.coprime_comm.mp ((Nat.coprime_or_dvd_of_prime hpp r).resolve_right
    fun h => absurd (Nat.le_of_dvd hr h) (by omega))).symm

/-- A prime dividing the block product is a block prime. -/
theorem mem_primeBlock_of_prime_dvd {r y q : ℕ} (hq : q.Prime) (hqP : q ∣ primeBlockProd r y) :
    q ∈ primeBlock r y := by
  obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqP
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
  linear_combination -h

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

/-! ## §3. The plateau carries pronic mass `1/(4r²y)` -/

/-- The plateau `[(r-1)(y + ⌊y/2r⌋), ry]` starts at a positive integer and has length `≥ y/2`. -/
private theorem plateau_window {r y : ℕ} (hr : 1 < r) (hry : r ≤ y) :
    1 ≤ (r - 1) * (y + y / (2 * r)) ∧
      2 * ((r - 1) * (y + y / (2 * r))) + y ≤ 2 * (r * y) := by
  set h := y / (2 * r)
  have hu : 2 * ((r - 1) * h) ≤ y :=
    calc 2 * ((r - 1) * h) ≤ 2 * (r * h) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right h (Nat.sub_le r 1))
      _ = h * (2 * r) := by ring
      _ ≤ y := Nat.div_mul_le_self y (2 * r)
  have hry' : r * y = (r - 1) * y + y := by
    conv_lhs => rw [← Nat.sub_add_cancel hr.le]
    ring
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega : 0 < y) (Nat.le_add_right y h)))), ?_⟩
  rw [Nat.mul_add, hry']
  generalize (r - 1) * y = t
  generalize (r - 1) * h = u at hu ⊢
  omega

/-- **Plateau lower bound.** If `|w(1)| ≤ 1` and `B_r ≤ φ(r)|∑_{p ∈ S_y} w(p)p^{-ε}|`, then on
the plateau `|Ψ| ≥ φ(r)|∑ w(p)p^{-ε}| - B_r`, and the plateau has pronic mass `≥ 1/(4r²y)`. -/
theorem plateau_le_signedDilationDirichletForm (w : ℕ → ℝ) (ε : ℝ) {r y : ℕ} (hr : 1 < r)
    (hry : r ≤ y) (hw1 : |w 1| ≤ 1)
    (hM : pmRamanujanPrimitiveBound r ≤
      (r.totient : ℝ) * |∑ p ∈ primeBlock r y, w p * (p : ℝ) ^ (-ε)|) :
    ((r.totient : ℝ) * |∑ p ∈ primeBlock r y, w p * (p : ℝ) ^ (-ε)| -
        pmRamanujanPrimitiveBound r) ^ 2 / (4 * (r : ℝ) ^ 2 * y) ≤
      signedDilationDirichletForm w ε (primeBlockProd r y).divisors r hr := by
  set S := ∑ p ∈ primeBlock r y, w p * (p : ℝ) ^ (-ε)
  set B := pmRamanujanPrimitiveBound r
  set φ : ℝ := (r.totient : ℝ)
  set a := (r - 1) * (y + y / (2 * r))
  obtain ⟨ha1, hab⟩ := plateau_window hr hry
  have hD : ∀ d ∈ (primeBlockProd r y).divisors, 0 < d := fun d hd => Nat.pos_of_mem_divisors hd
  have hφ : 0 ≤ φ := Nat.cast_nonneg _
  have hK : 0 ≤ φ * |S| - B := sub_nonneg.mpr hM
  have hpt : ∀ n ∈ Ico a (r * y + 1),
      (φ * |S| - B) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
        signedDilationPrimitive w ε (primeBlockProd r y).divisors r n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := mem_Ico.mp hn
    rw [signedDilationPrimitive_primeBlockProd_eq w ε hr hry hn1 (by omega), mul_one_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hC : |w 1 * (pmRamanujanPrimitive r n).re| ≤ B := by
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hw1).trans
        ((Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hr n))
    have hlow : φ * |S| - B ≤ |w 1 * (pmRamanujanPrimitive r n).re - φ * S| := by
      have h1 := abs_sub_abs_le_abs_sub (φ * S) (w 1 * (pmRamanujanPrimitive r n).re)
      rw [abs_mul, abs_of_nonneg hφ, abs_sub_comm] at h1
      linarith
    calc (φ * |S| - B) ^ 2 ≤ |w 1 * (pmRamanujanPrimitive r n).re - φ * S| ^ 2 :=
          pow_le_pow_left₀ hK hlow 2
      _ = _ := sq_abs _
  have hmass : 1 / (4 * (r : ℝ) ^ 2 * y) ≤
      ∑ n ∈ Ico a (r * y + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [sum_Ico_reciprocal_pronic (by omega) (by omega)]
    have hA : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hAB : 2 * (a : ℝ) + y ≤ 2 * ((r : ℝ) * y) := by exact_mod_cast hab
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.le
    have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (hr.le.trans hry)
    have hRY : (1 : ℝ) ≤ r * y := one_le_mul_of_one_le_of_one_le hr1 hy1
    push_cast
    rw [div_sub_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hAle : (a : ℝ) ≤ r * y := by linarith
    calc 1 * ((a : ℝ) * ((r : ℝ) * y + 1)) ≤ ((r : ℝ) * y) * (2 * ((r : ℝ) * y)) := by
          rw [one_mul]
          exact mul_le_mul hAle (by linarith) (by positivity) (by positivity)
      _ = (y / 2) * (4 * (r : ℝ) ^ 2 * y) := by ring
      _ ≤ (1 * ((r : ℝ) * y + 1) - a * 1) * (4 * (r : ℝ) ^ 2 * y) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc (φ * |S| - B) ^ 2 / (4 * (r : ℝ) ^ 2 * y)
      = (φ * |S| - B) ^ 2 * (1 / (4 * (r : ℝ) ^ 2 * y)) := by rw [mul_one_div]
    _ ≤ (φ * |S| - B) ^ 2 * ∑ n ∈ Ico a (r * y + 1), 1 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = ∑ n ∈ Ico a (r * y + 1), (φ * |S| - B) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ Ico a (r * y + 1), signedDilationPrimitive w ε (primeBlockProd r y).divisors r n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) := Finset.sum_le_sum hpt
    _ ≤ signedDilationDirichletForm w ε (primeBlockProd r y).divisors r hr :=
        sum_Ico_signedDilationPrimitive_sq_le w ε hD hr ha1

/-! ## §4. The prime mass of the block -/

/-- The relative prime number theorem `|θ(x) - x| ≤ η x` for all large `x`. -/
private theorem eventually_abs_theta_sub_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, |θ x - x| ≤ η * x := by
  filter_upwards [chebyshev_asymptotic.isLittleO.def hη, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx

/-- `θ(y + h) - θ(y)` is the logarithmic mass of the primes in `(y, y + h]`. -/
private theorem theta_add_sub_theta (y h : ℕ) :
    θ ((y + h : ℕ) : ℝ) - θ (y : ℝ) = ∑ p ∈ (Ioc y (y + h)).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast, sub_eq_iff_eq_add,
    Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_Ioc_consecutive _ (Nat.zero_le y) (Nat.le_add_right y h), add_comm]

/-- **Prime mass of the block.** By the prime number theorem, for `ε ≥ 0` and all large `y`,
`∑_{p ∈ S_y} p^{-ε} ≥ (2y)^{1-ε}/(16 r log 2y)`: the block has logarithmic mass `≥ y/(8r)` and
each of its primes has `p^{-ε} ≥ (2y)^{-ε} log p / log 2y`. -/
theorem eventually_primeBlock_rpow_mass_ge {r : ℕ} (hr : 1 < r) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᶠ y : ℕ in atTop,
      (2 * (y : ℝ)) ^ (1 - ε) / (16 * r * Real.log (2 * y)) ≤
        ∑ p ∈ primeBlock r y, (p : ℝ) ^ (-ε) := by
  have hR : (0 : ℝ) < r := by exact_mod_cast (zero_lt_one.trans hr)
  obtain ⟨X, hX⟩ :=
    eventually_atTop.mp (eventually_abs_theta_sub_le (η := 1 / (16 * r)) (by positivity))
  refine eventually_atTop.mpr ⟨max (6 * r) ⌈X⌉₊, fun y hy => ?_⟩
  have hy6 : 6 * r ≤ y := le_of_max_le_left hy
  have hyX : X ≤ y := (Nat.le_ceil X).trans (by exact_mod_cast le_of_max_le_right hy)
  set h := y / (2 * r)
  have hY : (6 : ℝ) * r ≤ y := by exact_mod_cast hy6
  have hhlow : (y : ℝ) - 2 * r ≤ 2 * r * h := by
    have h0 : y < h * (2 * r) + 2 * r := Nat.lt_div_mul_add (by omega)
    have h0' : (y : ℝ) < h * (2 * r) + 2 * r := by exact_mod_cast h0
    linarith
  have hhy : (h : ℝ) ≤ y := by exact_mod_cast Nat.div_le_self y (2 * r)
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have h1 := hX (y : ℝ) hyX
  have h2 := hX ((y + h : ℕ) : ℝ) (by push_cast; linarith)
  have hlog : (y : ℝ) / (8 * r) ≤ ∑ p ∈ primeBlock r y, Real.log p := by
    rw [primeBlock, ← theta_add_sub_theta]
    push_cast at h2 ⊢
    rw [abs_le] at h1 h2
    have hkey : (y : ℝ) / (8 * r) ≤ h - 1 / (16 * (r : ℝ)) * (2 * y + h) := by
      have e : (y : ℝ) / (8 * r) = 1 / (16 * (r : ℝ)) * (2 * y) := by
        field_simp
        ring
      have hmain : 1 / (16 * (r : ℝ)) * (4 * y + h) ≤ h := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith
      rw [e]
      linarith
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.le
  have hy2 : (1 : ℝ) < 2 * y := by linarith
  have hL : 0 < Real.log (2 * y) := Real.log_pos hy2
  have hper : ∀ p ∈ primeBlock r y,
      (2 * (y : ℝ)) ^ (-ε) / Real.log (2 * y) * Real.log p ≤ (p : ℝ) ^ (-ε) := by
    intro p hp
    obtain ⟨hpp, hyp, hpy⟩ := mem_primeBlock.mp hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hp2 : (p : ℝ) ≤ 2 * y := by
      have : p ≤ y + h := hpy
      have : (p : ℝ) ≤ y + h := by exact_mod_cast this
      linarith
    have hlp : Real.log p ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hp2
    have hlp0 : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hrp : (2 * (y : ℝ)) ^ (-ε) ≤ (p : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hp2 (by linarith)
    calc (2 * (y : ℝ)) ^ (-ε) / Real.log (2 * y) * Real.log p
        = (2 * (y : ℝ)) ^ (-ε) * (Real.log p / Real.log (2 * y)) := by ring
      _ ≤ (2 * (y : ℝ)) ^ (-ε) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hL).mpr hlp) (by positivity)
      _ ≤ (p : ℝ) ^ (-ε) := by rw [mul_one]; exact hrp
  have hpow : (2 * (y : ℝ)) ^ (1 - ε) = 2 * y * (2 * (y : ℝ)) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
  calc (2 * (y : ℝ)) ^ (1 - ε) / (16 * r * Real.log (2 * y))
      = (2 * (y : ℝ)) ^ (-ε) / Real.log (2 * y) * ((y : ℝ) / (8 * r)) := by
        rw [hpow]
        field_simp
        ring
    _ ≤ (2 * (y : ℝ)) ^ (-ε) / Real.log (2 * y) * ∑ p ∈ primeBlock r y, Real.log p :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = ∑ p ∈ primeBlock r y, (2 * (y : ℝ)) ^ (-ε) / Real.log (2 * y) * Real.log p :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ primeBlock r y, (p : ℝ) ^ (-ε) := Finset.sum_le_sum hper

/-! ## §5. Growth along the block products -/

/-- **Growth law.** Let `|w(1)| ≤ 1` and let `w` take one sign `η`, `|η| = 1`, on the primes. For
`0 ≤ ε < 1` the form on the block product eventually dominates
`φ(r)²/(2048 r⁴) · (2y)^{1-2ε}/log²(2y)`. -/
theorem eventually_signedDilationDirichletForm_ge (w : ℕ → ℝ) {η : ℝ} (hη : |η| = 1)
    (hw1 : |w 1| ≤ 1) (hwp : ∀ p : ℕ, p.Prime → w p = η) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    {r : ℕ} (hr : 1 < r) :
    ∀ᶠ y : ℕ in atTop,
      (r.totient : ℝ) ^ 2 / (2048 * (r : ℝ) ^ 4) *
          ((2 * (y : ℝ)) ^ (1 - 2 * ε) / Real.log (2 * y) ^ 2) ≤
        signedDilationDirichletForm w ε (primeBlockProd r y).divisors r hr := by
  set φ : ℝ := (r.totient : ℝ)
  set B := pmRamanujanPrimitiveBound r
  have hR : (0 : ℝ) < r := by exact_mod_cast (zero_lt_one.trans hr)
  have hφ1 : (1 : ℝ) ≤ φ := Nat.one_le_cast.mpr (Nat.totient_pos.mpr (by omega : 0 < r))
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set g : ℕ → ℝ := fun y => (2 * (y : ℝ)) ^ (1 - ε) / (16 * r * Real.log (2 * y))
  have hg : Tendsto g atTop atTop := by
    have h2 : Tendsto (fun y : ℕ => 2 * (y : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop two_pos
    refine (((tendsto_rpow_div_log_atTop_of_pos (by linarith : (0 : ℝ) < 1 - ε)).comp
      h2).atTop_div_const (by positivity : (0 : ℝ) < 16 * r)).congr fun y => ?_
    simp only [g, Function.comp]
    rw [div_div, mul_comm (Real.log _)]
  filter_upwards [eventually_primeBlock_rpow_mass_ge hr hε0, hg.eventually_ge_atTop (2 * B / φ),
    eventually_ge_atTop r] with y hM hgB hry
  have hsum : |∑ p ∈ primeBlock r y, w p * (p : ℝ) ^ (-ε)| =
      ∑ p ∈ primeBlock r y, (p : ℝ) ^ (-ε) := by
    rw [Finset.sum_congr rfl fun p hp => by rw [hwp p (mem_primeBlock.mp hp).1],
      ← Finset.mul_sum, abs_mul, hη, one_mul,
      abs_of_nonneg (Finset.sum_nonneg fun p _ => by positivity)]
  set M := ∑ p ∈ primeBlock r y, (p : ℝ) ^ (-ε)
  have hgB' : 2 * B ≤ φ * g y := by
    rw [div_le_iff₀ (by linarith)] at hgB
    linarith
  have hφM : φ * g y ≤ φ * M := mul_le_mul_of_nonneg_left hM (by linarith)
  have hplateau := plateau_le_signedDilationDirichletForm w ε hr hry hw1 (by rw [hsum]; linarith)
  rw [hsum] at hplateau
  refine le_trans ?_ hplateau
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (hr.le.trans hry)
  have hX : (0 : ℝ) < 2 * y := by linarith
  have hL : 0 < Real.log (2 * y) := Real.log_pos (by linarith)
  have hsq : (φ * g y / 2) ^ 2 ≤ (φ * M - B) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hu : (2 * (y : ℝ)) ^ (1 - ε) * (2 * (y : ℝ)) ^ (1 - ε) =
      2 * y * (2 * (y : ℝ)) ^ (1 - 2 * ε) := by
    rw [← Real.rpow_add hX, show (1 - ε) + (1 - ε) = 1 + (1 - 2 * ε) by ring,
      Real.rpow_add hX, Real.rpow_one]
  calc φ ^ 2 / (2048 * (r : ℝ) ^ 4) * ((2 * (y : ℝ)) ^ (1 - 2 * ε) / Real.log (2 * y) ^ 2)
      = φ ^ 2 * (2 * y * (2 * (y : ℝ)) ^ (1 - 2 * ε)) /
          (4096 * (r : ℝ) ^ 4 * Real.log (2 * y) ^ 2 * y) := by
        field_simp
        ring
    _ = φ ^ 2 * ((2 * (y : ℝ)) ^ (1 - ε) * (2 * (y : ℝ)) ^ (1 - ε)) /
          (4096 * (r : ℝ) ^ 4 * Real.log (2 * y) ^ 2 * y) := by rw [hu]
    _ = (φ * g y / 2) ^ 2 / (4 * (r : ℝ) ^ 2 * y) := by
        simp only [g]
        field_simp
        ring
    _ ≤ (φ * M - B) ^ 2 / (4 * (r : ℝ) ^ 2 * y) :=
        div_le_div_of_nonneg_right hsq (by positivity)

/-- **Divergence below half damping.** Under the hypotheses of the growth law and `ε < 1/2`, the
form tends to `+∞` along the block products: `(2y)^{1-2ε}/log²(2y) → ∞`. -/
theorem tendsto_signedDilationDirichletForm_primeBlockProd (w : ℕ → ℝ) {η : ℝ} (hη : |η| = 1)
    (hw1 : |w 1| ≤ 1) (hwp : ∀ p : ℕ, p.Prime → w p = η) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < 1 / 2) {r : ℕ} (hr : 1 < r) :
    Tendsto (fun y : ℕ => signedDilationDirichletForm w ε (primeBlockProd r y).divisors r hr)
      atTop atTop := by
  have hc : 0 < (r.totient : ℝ) ^ 2 / (2048 * (r : ℝ) ^ 4) := by
    have : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega : 0 < r))
    positivity
  have h2 : Tendsto (fun y : ℕ => 2 * (y : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop two_pos
  have hbase := ((tendsto_pow_atTop two_ne_zero).comp
    ((tendsto_rpow_div_log_atTop_of_pos (by linarith : (0 : ℝ) < (1 - 2 * ε) / 2)).comp
      h2)).const_mul_atTop hc
  have hlim : Tendsto (fun y : ℕ => (r.totient : ℝ) ^ 2 / (2048 * (r : ℝ) ^ 4) *
      ((2 * (y : ℝ)) ^ (1 - 2 * ε) / Real.log (2 * y) ^ 2)) atTop atTop := by
    refine hbase.congr fun y => ?_
    simp only [Function.comp, div_pow]
    rw [← Real.rpow_natCast ((2 * (y : ℝ)) ^ ((1 - 2 * ε) / 2)),
      ← Real.rpow_mul (by positivity)]
    norm_num
  exact tendsto_atTop_mono'
    atTop (eventually_signedDilationDirichletForm_ge w hη hw1 hwp hε0 (by linarith) hr) hlim

/-! ## §6. The hypercube form and its parity twin: the sign-blind threshold -/

/-- The parity twin of the hypercube form: every Möbius sign replaced by `+1`. -/
def hypercubeTwinDilationDirichletForm (ε : ℝ) (P r : ℕ) (hr : 1 < r) : ℝ :=
  signedDilationDirichletForm (fun _ => 1) ε P.divisors r hr

theorem moebiusReal_one' : moebiusReal 1 = 1 := by simp [moebiusReal]

theorem moebiusReal_of_prime {p : ℕ} (hp : p.Prime) : moebiusReal p = -1 := by
  simp [moebiusReal, ArithmeticFunction.moebius_apply_prime hp]

/-- **The hypercube form diverges below half damping.** For every `r > 1` and `0 ≤ ε < 1/2`,
`D_{r,ε}(P_y) → ∞` along the block products. -/
theorem tendsto_hypercubeDilationDirichletForm_primeBlockProd {r : ℕ} (hr : 1 < r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    Tendsto (fun y : ℕ => hypercubeDilationDirichletForm ε (primeBlockProd r y) r hr)
      atTop atTop :=
  tendsto_signedDilationDirichletForm_primeBlockProd moebiusReal (η := -1) (by simp)
    (by rw [moebiusReal_one', abs_one]) (fun _ hp => moebiusReal_of_prime hp) hε0 hε hr

/-- The parity twin diverges along the same block products. -/
theorem tendsto_hypercubeTwinDilationDirichletForm_primeBlockProd {r : ℕ} (hr : 1 < r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    Tendsto (fun y : ℕ => hypercubeTwinDilationDirichletForm ε (primeBlockProd r y) r hr)
      atTop atTop :=
  tendsto_signedDilationDirichletForm_primeBlockProd (fun _ => 1) (η := 1) (by simp)
    (by simp) (fun _ _ => rfl) hε0 hε hr

/-- **No cutoff-uniform bound below half damping.** For every `r > 1` and `0 ≤ ε < 1/2` the
hypercube Dirichlet form is unbounded over the squarefree cutoffs coprime to `r`. -/
theorem not_bddAbove_hypercubeDilationDirichletForm {r : ℕ} (hr : 1 < r) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ¬ BddAbove ((fun P => hypercubeDilationDirichletForm ε P r hr) ''
      {P : ℕ | Squarefree P ∧ Nat.Coprime P r}) := by
  rintro ⟨C, hC⟩
  obtain ⟨y, hyC, hyr⟩ :=
    (((tendsto_hypercubeDilationDirichletForm_primeBlockProd hr hε0 hε).eventually_gt_atTop C).and
      (eventually_ge_atTop r)).exists
  exact absurd (hC ⟨primeBlockProd r y,
    ⟨squarefree_primeBlockProd r y, coprime_primeBlockProd (by omega) hyr⟩, rfl⟩) (not_le.mpr hyC)

/-- Above half damping every weight bounded by one gives a cutoff-uniform bound. -/
theorem signedDilationDirichletForm_le_tsum_sq_of_half_lt (w : ℕ → ℝ) (hw : ∀ d, |w d| ≤ 1)
    {ε : ℝ} (hε : 1 / 2 < ε) (P : ℕ) {r : ℕ} (hr : 1 < r) :
    signedDilationDirichletForm w ε P.divisors r hr ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ^ 2 * pmRamanujanPrimitiveGram r r := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ) - ε)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hdiv_le : (∑ d ∈ P.divisors, (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ≤
      ∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ) - ε) :=
    hsum.sum_le_tsum P.divisors fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hG0 : 0 ≤ pmRamanujanPrimitiveGram r r := (pmRamanujanPrimitiveGram_pos hr).le
  have hterm : ∀ d₁ ∈ P.divisors, ∀ d₂ ∈ P.divisors,
      (w d₁ * (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) * (w d₂ * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε)) *
          pmRamanujanDilationProfile r hr ((d₁ : ℝ) / d₂) ≤
        (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
          pmRamanujanPrimitiveGram r r := by
    intro d₁ hd₁ d₂ hd₂
    have hd₁0 : (0 : ℝ) < d₁ := by exact_mod_cast Nat.pos_of_mem_divisors hd₁
    have hd₂0 : (0 : ℝ) < d₂ := by exact_mod_cast Nat.pos_of_mem_divisors hd₂
    have hw' : ∀ {d : ℝ} (_ : 0 < d) (c : ℝ), |c| ≤ 1 →
        |c * d ^ (-(1 / 2 : ℝ) - ε)| ≤ d ^ (-(1 / 2 : ℝ) - ε) := by
      intro d hd c hc
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hd _)]
      exact mul_le_of_le_one_left (by positivity) hc
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hw' hd₁0 _ (hw d₁)) (hw' hd₂0 _ (hw d₂)) (abs_nonneg _)
      (by positivity)) (abs_pmRamanujanDilationProfile_le hr (div_pos hd₁0 hd₂0))
      (abs_nonneg _) (by positivity)
  calc signedDilationDirichletForm w ε P.divisors r hr
      ≤ ∑ d₁ ∈ P.divisors, ∑ d₂ ∈ P.divisors,
          (d₁ : ℝ) ^ (-(1 / 2 : ℝ) - ε) * (d₂ : ℝ) ^ (-(1 / 2 : ℝ) - ε) *
            pmRamanujanPrimitiveGram r r :=
        Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm d₁ hd₁ d₂ hd₂
    _ = (∑ d ∈ P.divisors, (d : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ^ 2 * pmRamanujanPrimitiveGram r r := by
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d₁ _ => ?_
        rw [Finset.sum_mul]
    _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-(1 / 2 : ℝ) - ε)) ^ 2 * pmRamanujanPrimitiveGram r r :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hdiv_le 2) hG0

/-- **Sign-blind threshold of the hypercube form.** For every `r > 1`, the hypercube Dirichlet
form and its parity twin are bounded uniformly in the cutoff for `ε > 1/2`, and both diverge along
the block products for every `0 ≤ ε < 1/2`. The threshold does not see the Möbius sign. -/
theorem hypercubeDilationDirichletForm_threshold {r : ℕ} (hr : 1 < r) :
    (∀ ε : ℝ, 1 / 2 < ε → ∃ C : ℝ, ∀ P : ℕ,
        hypercubeDilationDirichletForm ε P r hr ≤ C ∧
          hypercubeTwinDilationDirichletForm ε P r hr ≤ C) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 →
        Tendsto (fun y : ℕ => hypercubeDilationDirichletForm ε (primeBlockProd r y) r hr)
          atTop atTop ∧
        Tendsto (fun y : ℕ => hypercubeTwinDilationDirichletForm ε (primeBlockProd r y) r hr)
          atTop atTop) :=
  ⟨fun ε hε => ⟨_, fun P => ⟨hypercubeDilationDirichletForm_le_tsum_sq_of_half_lt hε P hr,
      signedDilationDirichletForm_le_tsum_sq_of_half_lt _ (fun _ => by simp) hε P hr⟩⟩,
    fun _ hε0 hε => ⟨tendsto_hypercubeDilationDirichletForm_primeBlockProd hr hε0 hε,
      tendsto_hypercubeTwinDilationDirichletForm_primeBlockProd hr hε0 hε⟩⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
