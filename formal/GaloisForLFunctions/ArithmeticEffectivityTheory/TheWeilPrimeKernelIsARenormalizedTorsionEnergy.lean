import GaloisForLFunctions.ArithmeticEffectivityTheory.TheIntersectionOfTorsionOrbits

/-!
# Weil's prime kernel is a renormalized torsion energy

The prime side of Weil's form, restricted to atoms at `log n`, is the kernel
`P(m, n) = Λ(n/m) (n/m)^{−1/2}` on pairs `m ∣ n`. This file shows it is the renormalized limit of a
family of positive semidefinite forms built from the torsion of the circle.

* **The Abel energy** (`torsionEnergy`, `hasSum_torsionEnergy`). For `0 ≤ r < 1` let
  `T_r(m, n) = Σ_{ζ ∈ O_m, η ∈ O_n} −log |1 − r ζ η̄|`. Since `−log |1 − w| = Σ_k Re(w^k)/k`,
  `T_r(m, n) = Σ_k (r^k/k) c_m(k) c_n(k)` with the Ramanujan sums `c_n(k)`: a Gram matrix, positive
  semidefinite (`sum_sum_torsionEnergy_nonneg`).
* **The gcd twist** (`gcdTwist`, `sum_divisors_twistWeight`). `G(m, n) = Σ_{e ∣ (m, n)} μ(e)²/φ(e)`
  is positive semidefinite and equals `d/φ(d)` at `d = gcd(m, n)`. The Schur product of `G` with
  the energy stays positive (`sum_sum_gcdTwist_torsionEnergy_nonneg`).
* **The limit** (`tendsto_twistedEnergy_of_ne`, `tendsto_twistedEnergy_self_add_log`). The twisted
  energy `G(m, n) T_r(m, n)/√(mn)` tends to `−P(m, n)` off the diagonal: by the intersection law
  `T_1(m, mt) = −φ(m)Λ(t)`, and `G` turns `φ(m)` into `m`. On the diagonal it diverges like
  `−log(1 − r)`; after renormalization it tends to `−I(n, n)/φ(n)`, minus the log-discriminant
  per point.

So (`weilPrimeKernel_renormalized_torsion_energy`) the discrete Weil prime form plus the
log-discriminant diagonal is minus the renormalized limit of a positive torsion energy. The sign of
the energy is lost exactly in the renormalization `log(1/(1 − r)) Σ x_n²`: positivity of the
regularized forms bounds the prime form only by the divergent self-energy.
-/

noncomputable section

open Finset Complex Filter Topology
open scoped Real ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ComplexConjugate

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-! ### The Abel energy of torsion orbits -/

/-- `−log |1 − r w| = Σ_k r^k Re(w^k)/k` for `‖w‖ ≤ 1`, `0 ≤ r < 1`. -/
theorem hasSum_neg_log_norm_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    HasSum (fun k : ℕ => r ^ k / k * (w ^ k).re) (-Real.log ‖1 - (r : ℂ) * w‖) := by
  have hz : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    nlinarith [norm_nonneg w]
  have h := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hz)
  simp only [Complex.reCLM_apply, Complex.neg_re, Complex.log_re] at h
  convert h using 2 with k
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.re_ofReal_mul]
  ring

theorem norm_of_mem_primitiveRoots {n : ℕ} {ζ : ℂ} (h : ζ ∈ primitiveRoots n ℂ) : ‖ζ‖ = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · exact Complex.norm_eq_one_of_pow_eq_one ((mem_primitiveRoots hn).mp h).pow_eq_one hn.ne'

/-- `|1 − ζ η̄| = |ζ − η|` on the unit circle. -/
theorem norm_one_sub_mul_conj {ζ η : ℂ} (hη : ‖η‖ = 1) : ‖1 - ζ * conj η‖ = ‖ζ - η‖ := by
  have h1 : η * conj η = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hη]; simp
  calc ‖1 - ζ * conj η‖ = ‖η * (1 - ζ * conj η)‖ := by rw [norm_mul, hη, one_mul]
    _ = ‖ζ - η‖ := by
      rw [mul_sub, mul_one, show η * (ζ * conj η) = ζ * (η * conj η) by ring, h1, mul_one,
        norm_sub_rev]

/-- The **Abel energy** `T_r(m, n) = Σ_{ζ ∈ O_m, η ∈ O_n} −log |1 − r ζ η̄|`. -/
def torsionEnergy (r : ℝ) (m n : ℕ) : ℝ :=
  ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, -Real.log ‖1 - (r : ℂ) * (ζ * conj η)‖

/-- `T_r(m, n) = Σ_k (r^k/k) Re(c_m(k) \overline{c_n(k)})`. -/
theorem hasSum_torsionEnergy {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m n : ℕ) :
    HasSum (fun k : ℕ => r ^ k / k * (ramanujanSum m k * conj (ramanujanSum n k)).re)
      (torsionEnergy r m n) := by
  have h := hasSum_sum fun ζ (hζ : ζ ∈ primitiveRoots m ℂ) => hasSum_sum
    fun η (hη : η ∈ primitiveRoots n ℂ) => hasSum_neg_log_norm_one_sub hr0 hr1
      (w := ζ * conj η) (by
        rw [norm_mul, Complex.norm_conj, norm_of_mem_primitiveRoots hζ,
          norm_of_mem_primitiveRoots hη, one_mul])
  rw [torsionEnergy]
  convert h using 1
  funext k
  rw [ramanujanSum, ramanujanSum, map_sum, sum_mul_sum, Complex.re_sum, mul_sum]
  refine sum_congr rfl fun ζ _ => ?_
  rw [Complex.re_sum, mul_sum]
  refine sum_congr rfl fun η _ => ?_
  rw [mul_pow, map_pow]

/-- **Energy positivity**: `Σ_{m,n} y_m y_n T_r(m, n) = Σ_k (r^k/k) |Σ_n y_n c_n(k)|² ≥ 0`. -/
theorem sum_sum_torsionEnergy_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ)
    (y : ℕ → ℝ) : 0 ≤ ∑ m ∈ S, ∑ n ∈ S, y m * y n * torsionEnergy r m n := by
  have h := hasSum_sum fun m (_ : m ∈ S) => hasSum_sum fun n (_ : n ∈ S) =>
    (hasSum_torsionEnergy hr0 hr1 m n).mul_left (y m * y n)
  refine h.nonneg fun k => ?_
  have hsq : ∑ m ∈ S, ∑ n ∈ S,
      y m * y n * (r ^ k / k * (ramanujanSum m k * conj (ramanujanSum n k)).re) =
      r ^ k / k * Complex.normSq (∑ m ∈ S, (y m : ℂ) * ramanujanSum m k) := by
    rw [← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum, sum_mul_sum,
      Complex.re_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Complex.re_sum, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [map_mul, Complex.conj_ofReal, show (y m : ℂ) * ramanujanSum m k *
      ((y n : ℂ) * conj (ramanujanSum n k)) = ((y m * y n : ℝ) : ℂ) *
        (ramanujanSum m k * conj (ramanujanSum n k)) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  rw [hsq]
  exact mul_nonneg (div_nonneg (pow_nonneg hr0 k) (Nat.cast_nonneg k)) (Complex.normSq_nonneg _)

/-! ### The gcd twist -/

/-- The weight `μ(e)²/φ(e)` of the squarefree divisors. -/
def twistWeight (e : ℕ) : ℝ := (μ e : ℝ) ^ 2 / Nat.totient e

theorem twistWeight_nonneg (e : ℕ) : 0 ≤ twistWeight e :=
  div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem cast_totient_prime {p : ℕ} (hp : p.Prime) : (Nat.totient p : ℝ) = p - 1 := by
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]

/-- On a prime power `p^i`, `i ≥ 1`, both `Σ_{e ∣ p^i} μ(e)²/φ(e)` and `p^i/φ(p^i)` are
`1 + 1/(p − 1)`. -/
theorem sum_range_twistWeight_prime_pow {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 1 ≤ i) :
    ∑ j ∈ range (i + 1), twistWeight (p ^ j) = 1 + 1 / ((p : ℝ) - 1) := by
  induction i, hi using Nat.le_induction with
  | base =>
    simp [Finset.sum_range_succ, twistWeight, ArithmeticFunction.moebius_apply_prime hp,
      cast_totient_prime hp]
  | succ i hi ih =>
    rw [Finset.sum_range_succ, ih, twistWeight,
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp

theorem prime_pow_div_totient {p : ℕ} (hp : p.Prime) {i : ℕ} (hi : 1 ≤ i) :
    ((p ^ i : ℕ) : ℝ) / Nat.totient (p ^ i) = 1 + 1 / ((p : ℝ) - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_sub hp.one_lt.le]
  push_cast
  field_simp
  ring

/-- `Σ_{e ∣ n} μ(e)²/φ(e) = n/φ(n)`. -/
theorem sum_divisors_twistWeight (n : ℕ) :
    ∑ e ∈ n.divisors, twistWeight e = n / Nat.totient n := by
  let f : ArithmeticFunction ℝ := ⟨twistWeight, by simp [twistWeight]⟩
  let g : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) / Nat.totient n, by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨by simp [f, twistWeight], fun {a b} hab => ?_⟩
    simp only [f, ArithmeticFunction.coe_mk, twistWeight]
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab, Nat.totient_mul hab]
    push_cast
    ring
  have hg : g.IsMultiplicative := by
    refine ⟨by simp [g], fun {a b} hab => ?_⟩
    simp only [g, ArithmeticFunction.coe_mk]
    rw [Nat.totient_mul hab]
    push_cast
    ring
  have key : f * ArithmeticFunction.zeta = g := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
      (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast) _ hg).mpr fun p i hp => ?_
    rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp only [f, g, ArithmeticFunction.coe_mk]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [twistWeight]
    · rw [sum_range_twistWeight_prime_pow hp hi, prime_pow_div_totient hp hi]
  have := congrArg (fun F : ArithmeticFunction ℝ => F n) key
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at this
  simpa only [f, g, ArithmeticFunction.coe_mk] using this

/-- The **gcd twist** `G(m, n) = Σ_{e ∣ gcd(m, n)} μ(e)²/φ(e)`. -/
def gcdTwist (m n : ℕ) : ℝ := ∑ e ∈ (Nat.gcd m n).divisors, twistWeight e

theorem gcdTwist_eq (m n : ℕ) : gcdTwist m n = Nat.gcd m n / Nat.totient (Nat.gcd m n) :=
  sum_divisors_twistWeight _

/-- **The twisted energy is positive** (Schur product of two positive kernels). -/
theorem sum_sum_gcdTwist_torsionEnergy_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {S : Finset ℕ}
    (hS : ∀ n ∈ S, 0 < n) (y : ℕ → ℝ) :
    0 ≤ ∑ m ∈ S, ∑ n ∈ S, y m * y n * (gcdTwist m n * torsionEnergy r m n) := by
  classical
  set E := S.biUnion Nat.divisors
  set z : ℕ → ℕ → ℝ := fun e m => if e ∣ m then y m else 0
  have hG : ∀ m ∈ S, ∀ n ∈ S, gcdTwist m n =
      ∑ e ∈ E, if e ∣ m ∧ e ∣ n then twistWeight e else 0 := by
    intro m hm n hn
    rw [gcdTwist, ← sum_filter]
    congr 1
    ext e
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, E, mem_biUnion]
    constructor
    · rintro ⟨⟨hem, hen⟩, -⟩
      exact ⟨⟨m, hm, hem, (hS m hm).ne'⟩, hem, hen⟩
    · rintro ⟨-, hem, hen⟩
      exact ⟨⟨hem, hen⟩, (Nat.gcd_pos_of_pos_left n (hS m hm)).ne'⟩
  have hpt : ∀ m ∈ S, ∀ n ∈ S, y m * y n * (gcdTwist m n * torsionEnergy r m n) =
      ∑ e ∈ E, twistWeight e * (z e m * z e n * torsionEnergy r m n) := by
    intro m hm n hn
    rw [hG m hm n hn, sum_mul, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    by_cases hem : e ∣ m <;> by_cases hen : e ∣ n <;> simp [z, hem, hen]; ring
  rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hpt m hm n hn]
  rw [sum_congr rfl fun m _ => sum_comm, sum_comm]
  refine sum_nonneg fun e _ => ?_
  simp_rw [← mul_sum]
  exact mul_nonneg (twistWeight_nonneg e) (sum_sum_torsionEnergy_nonneg hr0 hr1 S (z e))

/-! ### The limit at `r = 1` -/

/-- Off the diagonal the energy tends to `−I(m, n)`. -/
theorem tendsto_torsionEnergy_of_ne {m n : ℕ} (hmn : m ≠ n) :
    Tendsto (fun r : ℝ => torsionEnergy r m n) (𝓝 1) (𝓝 (-orbitIntersection m n)) := by
  have hval : -orbitIntersection m n = ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ,
      -Real.log ‖1 - ((1 : ℝ) : ℂ) * (ζ * conj η)‖ := by
    rw [orbitIntersection, ← sum_neg_distrib]
    refine sum_congr rfl fun ζ _ => ?_
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun η hη => ?_
    rw [Complex.ofReal_one, one_mul, norm_one_sub_mul_conj (norm_of_mem_primitiveRoots hη)]
  rw [hval]
  refine tendsto_finsetSum _ fun ζ hζ => tendsto_finsetSum _ fun η hη => ?_
  have hne : ζ ≠ η := by
    rintro rfl
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hζ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hη
    exact hmn (((mem_primitiveRoots hm).mp hζ).unique ((mem_primitiveRoots hn).mp hη))
  have hw : ‖1 - ((1 : ℝ) : ℂ) * (ζ * conj η)‖ ≠ 0 := by
    rw [Complex.ofReal_one, one_mul, norm_one_sub_mul_conj (norm_of_mem_primitiveRoots hη)]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact ((continuous_const.sub (Complex.continuous_ofReal.mul
    continuous_const)).norm.continuousAt.log hw).neg.tendsto

/-- The diagonal pairs carry `−log |1 − r|` each. -/
theorem torsionEnergy_self_add_log (r : ℝ) (n : ℕ) :
    torsionEnergy r n n + Nat.totient n * Real.log |1 - r| =
      ∑ ζ ∈ primitiveRoots n ℂ, ∑ η ∈ (primitiveRoots n ℂ).erase ζ,
        -Real.log ‖1 - (r : ℂ) * (ζ * conj η)‖ := by
  have hcard : ((primitiveRoots n ℂ).card : ℝ) = Nat.totient n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact_mod_cast (Complex.isPrimitiveRoot_exp n hn.ne').card_primitiveRoots
  have hdiag : ∀ ζ ∈ primitiveRoots n ℂ,
      -Real.log ‖1 - (r : ℂ) * (ζ * conj ζ)‖ = -Real.log |1 - r| := by
    intro ζ hζ
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_of_mem_primitiveRoots hζ,
      show (1 : ℂ) - (r : ℂ) * (((1 : ℝ) ^ 2 : ℝ) : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [torsionEnergy, sum_congr rfl fun ζ hζ => (add_sum_erase _ _ hζ).symm, sum_add_distrib,
    sum_congr rfl hdiag, sum_const, nsmul_eq_mul, hcard]
  ring

/-- On the diagonal the renormalized energy tends to `−I(n, n)`. -/
theorem tendsto_torsionEnergy_self_add_log (n : ℕ) :
    Tendsto (fun r : ℝ => torsionEnergy r n n + Nat.totient n * Real.log |1 - r|) (𝓝 1)
      (𝓝 (-orbitIntersection n n)) := by
  have hval : -orbitIntersection n n = ∑ ζ ∈ primitiveRoots n ℂ,
      ∑ η ∈ (primitiveRoots n ℂ).erase ζ, -Real.log ‖1 - ((1 : ℝ) : ℂ) * (ζ * conj η)‖ := by
    rw [orbitIntersection, ← sum_neg_distrib]
    refine sum_congr rfl fun ζ hζ => ?_
    rw [← add_sum_erase _ _ hζ, sub_self, norm_zero, Real.log_zero, zero_add, ← sum_neg_distrib]
    refine sum_congr rfl fun η hη => ?_
    rw [Complex.ofReal_one, one_mul,
      norm_one_sub_mul_conj (norm_of_mem_primitiveRoots (mem_of_mem_erase hη))]
  simp_rw [torsionEnergy_self_add_log]
  rw [hval]
  refine tendsto_finsetSum _ fun ζ _ => tendsto_finsetSum _ fun η hη => ?_
  have hw : ‖1 - ((1 : ℝ) : ℂ) * (ζ * conj η)‖ ≠ 0 := by
    rw [Complex.ofReal_one, one_mul,
      norm_one_sub_mul_conj (norm_of_mem_primitiveRoots (mem_of_mem_erase hη))]
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ne_of_mem_erase hη).symm)
  exact ((continuous_const.sub (Complex.continuous_ofReal.mul
    continuous_const)).norm.continuousAt.log hw).neg.tendsto

/-! ### Weil's prime kernel -/

/-- **Weil's prime kernel** on orders: `Λ(n/m) (n/m)^{−1/2}` for `m ∣ n`, `m ≠ n`, symmetric, and
`0` on the diagonal and on non-divisible pairs. -/
def weilPrimeKernel (m n : ℕ) : ℝ :=
  if m ∣ n ∧ m ≠ n then Λ (n / m) / Real.sqrt ((n / m : ℕ) : ℝ)
  else if n ∣ m ∧ n ≠ m then Λ (m / n) / Real.sqrt ((m / n : ℕ) : ℝ) else 0

/-- The twisted energy entry `G(m, n) T_r(m, n)/√(mn)`. -/
def twistedEnergy (r : ℝ) (m n : ℕ) : ℝ :=
  gcdTwist m n * torsionEnergy r m n / Real.sqrt ((m : ℝ) * n)

theorem sqrt_mul_mul_eq {d t : ℕ} : Real.sqrt ((d : ℝ) * ((d * t : ℕ) : ℝ)) =
    d * Real.sqrt t := by
  rw [Nat.cast_mul, ← mul_assoc, Real.sqrt_mul (mul_self_nonneg _),
    Real.sqrt_mul_self (Nat.cast_nonneg _)]

/-- The twist turns the intersection `φ(d) Λ(t)` of `O_d` with `O_{dt}` into `Λ(t)/√t`. -/
theorem gcdTwist_mul_orbitIntersection_hecke {d t : ℕ} (hd : 0 < d) (ht : 1 < t) :
    gcdTwist d (d * t) * orbitIntersection d (d * t) / Real.sqrt ((d : ℝ) * ((d * t : ℕ) : ℝ)) =
      Λ t / Real.sqrt t := by
  have hφ : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [gcdTwist_eq, Nat.gcd_eq_left (dvd_mul_right d t), orbitIntersection_hecke hd ht,
    sqrt_mul_mul_eq]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (t : ℝ)) with h | h
  · rw [← h]; simp
  · field_simp

theorem orbitIntersection_comm (m n : ℕ) : orbitIntersection m n = orbitIntersection n m := by
  rw [orbitIntersection, orbitIntersection, sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [norm_sub_rev]

theorem gcdTwist_comm (m n : ℕ) : gcdTwist m n = gcdTwist n m := by
  rw [gcdTwist, gcdTwist, Nat.gcd_comm]

/-- **Off the diagonal the twisted energy tends to minus Weil's prime kernel.** -/
theorem tendsto_twistedEnergy_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Tendsto (fun r : ℝ => twistedEnergy r m n) (𝓝 1) (𝓝 (-weilPrimeKernel m n)) := by
  have hlim := (tendsto_torsionEnergy_of_ne hmn).const_mul (gcdTwist m n / Real.sqrt ((m : ℝ) * n))
  have heq : (fun r : ℝ => twistedEnergy r m n) =
      fun r => gcdTwist m n / Real.sqrt ((m : ℝ) * n) * torsionEnergy r m n := by
    funext r; rw [twistedEnergy]; ring
  rw [heq]
  convert hlim using 2
  by_cases hdvd : m ∣ n
  · obtain ⟨t, rfl⟩ := hdvd
    have ht : 1 < t := by
      rcases Nat.lt_or_ge 1 t with h | h
      · exact h
      · interval_cases t
        · simp at hn
        · exact absurd (mul_one m).symm hmn
    rw [weilPrimeKernel, if_pos ⟨dvd_mul_right m t, hmn⟩, Nat.mul_div_cancel_left t hm,
      ← gcdTwist_mul_orbitIntersection_hecke hm ht]
    push_cast
    ring
  · by_cases hdvd' : n ∣ m
    · obtain ⟨t, rfl⟩ := hdvd'
      have ht : 1 < t := by
        rcases Nat.lt_or_ge 1 t with h | h
        · exact h
        · interval_cases t
          · simp at hm
          · exact absurd (mul_one n) hmn
      rw [weilPrimeKernel, if_neg (fun h => hdvd h.1), if_pos ⟨dvd_mul_right n t, Ne.symm hmn⟩,
        Nat.mul_div_cancel_left t hn, ← gcdTwist_mul_orbitIntersection_hecke hn ht,
        gcdTwist_comm, orbitIntersection_comm]
      push_cast
      ring_nf
    · rw [weilPrimeKernel, if_neg (fun h => hdvd h.1), if_neg (fun h => hdvd' h.1),
        orbitIntersection_eq hm hn hmn, if_neg hdvd', if_neg hdvd]
      simp

/-- **On the diagonal the renormalized twisted energy tends to `−I(n, n)/φ(n)`.** -/
theorem tendsto_twistedEnergy_self_add_log {n : ℕ} (hn : 0 < n) :
    Tendsto (fun r : ℝ => twistedEnergy r n n + Real.log |1 - r|) (𝓝 1)
      (𝓝 (-(orbitIntersection n n / Nat.totient n))) := by
  have hφ : (Nat.totient n : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (fun r : ℝ => twistedEnergy r n n + Real.log |1 - r|) =
      fun r => (torsionEnergy r n n + Nat.totient n * Real.log |1 - r|) / Nat.totient n := by
    funext r
    rw [twistedEnergy, gcdTwist_eq, Nat.gcd_self, Real.sqrt_mul_self (Nat.cast_nonneg _)]
    field_simp
  rw [heq, ← neg_div]
  exact (tendsto_torsionEnergy_self_add_log n).div_const _

/-- **Weil's prime kernel is a renormalized torsion energy.** For a finite set `S` of orders and
real weights `x`, the twisted energies `Q_r(x) = Σ_{m,n ∈ S} x_m x_n G(m, n) T_r(m, n)/√(mn)` are
nonnegative for `0 ≤ r < 1`, and `Q_r(x) + log |1 − r| Σ_n x_n²` tends, as `r → 1`, to
`−Σ_{m,n} x_m x_n P(m, n) − Σ_n x_n² I(n, n)/φ(n)`. -/
theorem weilPrimeKernel_renormalized_torsion_energy {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n)
    (x : ℕ → ℝ) :
    (∀ r : ℝ, 0 ≤ r → r < 1 → 0 ≤ ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n) ∧
    Tendsto (fun r : ℝ => ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n +
        Real.log |1 - r| * ∑ n ∈ S, x n ^ 2) (𝓝 1)
      (𝓝 (-(∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n) -
        ∑ n ∈ S, x n ^ 2 * (orbitIntersection n n / Nat.totient n))) := by
  refine ⟨fun r hr0 hr1 => ?_, ?_⟩
  · have h := sum_sum_gcdTwist_torsionEnergy_nonneg hr0 hr1 hS (fun n => x n / Real.sqrt n)
    convert h using 1
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    rw [twistedEnergy, Real.sqrt_mul (Nat.cast_nonneg _)]
    ring
  · classical
    have hsplit : ∀ F : ℕ → ℕ → ℝ, ∑ m ∈ S, ∑ n ∈ S, F m n =
        ∑ m ∈ S, (F m m + ∑ n ∈ S.erase m, F m n) :=
      fun F => sum_congr rfl fun m hm => (add_sum_erase _ _ hm).symm
    have hfun : (fun r : ℝ => ∑ m ∈ S, ∑ n ∈ S, x m * x n * twistedEnergy r m n +
        Real.log |1 - r| * ∑ n ∈ S, x n ^ 2) = fun r => ∑ m ∈ S,
          (x m ^ 2 * (twistedEnergy r m m + Real.log |1 - r|) +
            ∑ n ∈ S.erase m, x m * x n * twistedEnergy r m n) := by
      funext r
      rw [hsplit, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      ring
    have htarget : -(∑ m ∈ S, ∑ n ∈ S, x m * x n * weilPrimeKernel m n) -
        ∑ n ∈ S, x n ^ 2 * (orbitIntersection n n / Nat.totient n) = ∑ m ∈ S,
          (x m ^ 2 * -(orbitIntersection m m / Nat.totient m) +
            ∑ n ∈ S.erase m, x m * x n * -weilPrimeKernel m n) := by
      rw [hsplit, ← sum_neg_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun m _ => ?_
      have h0 : weilPrimeKernel m m = 0 := by simp [weilPrimeKernel]
      rw [h0, neg_add, ← sum_neg_distrib]
      simp only [mul_zero, neg_zero, zero_add, mul_neg]
      ring
    rw [hfun, htarget]
    refine tendsto_finsetSum _ fun m hm => ?_
    refine ((tendsto_twistedEnergy_self_add_log (hS m hm)).const_mul _).add
      (tendsto_finsetSum _ fun n hn => ?_)
    exact (tendsto_twistedEnergy_of_ne (hS m hm) (hS n (mem_of_mem_erase hn))
      (ne_of_mem_erase hn).symm).const_mul _

end GaloisForLFunctions.ArithmeticEffectivityTheory
