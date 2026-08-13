import GaloisForLFunctions.RHTower.Sieve.PrimeLogPowerTail
import GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialEdgeReflectedIdealGrade
import GaloisForLFunctions.RHTower.XiCanonicalProduct

/-!
# The reciprocal-log Fisher half-density entrance wall

The inverse prime-log potential `vₚ = √Fₚ / log p` of the positive Euler--Fisher half-density
`Fₚ = p/(p+1)²` is a genuine `ℓ²` vector and lies exactly at the first prime-log form wall: it
belongs to every strict fractional prime-log domain and falls out of the full domain, because
`Fₚ` is squeezed between `1/(4p)` and `1/p` while the prime reciprocal-log-power tail converges
for every positive exponent and the reciprocal-prime sum diverges.  The physical fixed-orientation
half-density transport `p^{t/2} vₚ` is square-summable precisely on the nonpositive centered-grade
side, the finite-truncation net is Cauchy precisely there, and for every nonzero scalar the
Xi-divisor coefficient field `c·p^{ρ-1/2} vₚ` lies in the fixed `ℓ²` carrier exactly when
`Re ρ ≤ 1/2`.  One explicit source vector detects every right-half Xi fibre by failure of
physical Cauchy landing.
-/

open Filter
open scoped BigOperators ENNReal

namespace RHTower

noncomputable section

/-- The inverse prime-log potential of the Euler--Fisher half-density. -/
def routeRFisherLogPotential (p : Nat.Primes) : ℝ :=
  Real.sqrt (primeActivationOccupancyFisherDensity p) / Real.log ((p : ℕ) : ℝ)

theorem primeActivationOccupancyFisherDensity_pos (p : Nat.Primes) :
    0 < primeActivationOccupancyFisherDensity p := by
  rw [primeActivationOccupancyFisherDensity_eq]
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  positivity

theorem primeActivationOccupancyFisherDensity_le_one_div (p : Nat.Primes) :
    primeActivationOccupancyFisherDensity p ≤ 1 / ((p : ℕ) : ℝ) := by
  have h := (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).1
  linarith

theorem one_div_four_mul_le_primeActivationOccupancyFisherDensity (p : Nat.Primes) :
    1 / (4 * ((p : ℕ) : ℝ)) ≤ primeActivationOccupancyFisherDensity p := by
  rw [primeActivationOccupancyFisherDensity_eq]
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem log_prime_pos (p : Nat.Primes) : 0 < Real.log ((p : ℕ) : ℝ) :=
  Real.log_pos (by exact_mod_cast p.2.one_lt)

theorem routeRFisherLogPotential_nonneg (p : Nat.Primes) :
    0 ≤ routeRFisherLogPotential p :=
  div_nonneg (Real.sqrt_nonneg _) (log_prime_pos p).le

/-- The squared potential is the Fisher density damped by the squared prime logarithm. -/
theorem routeRFisherLogPotential_sq (p : Nat.Primes) :
    routeRFisherLogPotential p ^ 2 =
      primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ 2 := by
  rw [routeRFisherLogPotential, div_pow,
    Real.sq_sqrt (primeActivationOccupancyFisherDensity_pos p).le]

/-! ## Theorem 1: maximal prime-log regularity -/

/-- **Strict fractional domains.**  For every `0 ≤ α < 1` the fractional prime-log energy
`∑ₚ Fₚ / (log p)^{2-2α}` converges: the potential lies in every strict fractional domain of the
prime-log derivation. -/
theorem summable_fisher_fractional_logDomain {α : ℝ} (hα : α < 1) :
    Summable fun p : Nat.Primes =>
      primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ (2 - 2 * α) := by
  have hs : 0 < 2 - 2 * α := by linarith
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    (Sieve.summable_primes_one_div_mul_log_rpow hs)
  · have hlog := Real.rpow_pos_of_pos (log_prime_pos p) (2 - 2 * α)
    have hF := (primeActivationOccupancyFisherDensity_pos p).le
    positivity
  · have hlog := Real.rpow_pos_of_pos (log_prime_pos p) (2 - 2 * α)
    have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show 1 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ (2 - 2 * α)) =
        (1 / ((p : ℕ) : ℝ)) / Real.log ((p : ℕ) : ℝ) ^ (2 - 2 * α) by field_simp]
    gcongr
    exact primeActivationOccupancyFisherDensity_le_one_div p

/-- **The full-domain wall.**  The raw Fisher half-density is not summable: the potential falls
out of the full prime-log domain, by Euler's divergence of the reciprocal-prime sum. -/
theorem not_summable_fisherDensity :
    ¬ Summable fun p : Nat.Primes => primeActivationOccupancyFisherDensity p := by
  intro hsum
  have hquarter : Summable fun p : Nat.Primes => 1 / (4 * ((p : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun p => by
        have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
        positivity)
      (fun p => one_div_four_mul_le_primeActivationOccupancyFisherDensity p) hsum
  have hharm : Summable fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) := by
    have h4 := hquarter.mul_left (4 : ℝ)
    refine h4.congr fun p => ?_
    have hp : ((p : ℕ) : ℝ) ≠ 0 := by
      have := p.2.pos
      positivity
    field_simp
  exact Nat.Primes.not_summable_one_div hharm

/-! ## Theorem 2: the one-sided physical entrance wall -/

/-- Squared physical transport of the potential at centered grade `t`. -/
theorem physical_transport_sq (t : ℝ) (p : Nat.Primes) :
    (((p : ℕ) : ℝ) ^ (t / 2) * routeRFisherLogPotential p) ^ 2 =
      ((p : ℕ) : ℝ) ^ t *
        (primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ 2) := by
  have hp : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  rw [mul_pow, routeRFisherLogPotential_sq, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (t / 2)) 2,
    ← Real.rpow_mul hp.le]
  norm_num

/-- **Exact one-sided entrance wall.**  The physical transport of the potential is square
summable exactly on the nonpositive centered-grade side. -/
theorem summable_physical_transport_sq_iff (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      (((p : ℕ) : ℝ) ^ (t / 2) * routeRFisherLogPotential p) ^ 2) ↔ t ≤ 0 := by
  constructor
  · -- a positive grade diverges: the transported density eventually dominates `1/p`
    intro hsum
    by_contra hpos
    push Not at hpos
    have hlittle := isLittleO_log_rpow_rpow_atTop 2 hpos
    rw [Asymptotics.isLittleO_iff] at hlittle
    have hev := hlittle (by norm_num : (0 : ℝ) < 1 / 4)
    rw [eventually_atTop] at hev
    obtain ⟨X₀, hX₀⟩ := hev
    -- all but finitely many primes exceed the threshold
    have hfin : {p : Nat.Primes | ((p : ℕ) : ℝ) < max X₀ 2}.Finite := by
      have hsub : {p : Nat.Primes | ((p : ℕ) : ℝ) < max X₀ 2} ⊆
          (fun p : Nat.Primes => (p : ℕ)) ⁻¹' {n : ℕ | (n : ℝ) < max X₀ 2} := fun p hp => hp
      refine Set.Finite.subset (Set.Finite.preimage ?_ ?_) hsub
      · intro p _ q _ hpq
        exact Subtype.ext hpq
      · have hsub2 : {n : ℕ | (n : ℝ) < max X₀ 2} ⊆ Set.Iio (Nat.ceil (max X₀ 2) + 1) := by
          intro n hn
          simp only [Set.mem_setOf_eq] at hn
          have hlt := Nat.lt_ceil.mpr hn
          simp only [Set.mem_Iio]
          omega
        exact (Set.finite_Iio _).subset hsub2
    have hcof : ∀ᶠ p : Nat.Primes in cofinite,
        1 / ((p : ℕ) : ℝ) ≤
          (((p : ℕ) : ℝ) ^ (t / 2) * routeRFisherLogPotential p) ^ 2 := by
      rw [eventually_cofinite]
      refine hfin.subset fun p hp => ?_
      simp only [Set.mem_setOf_eq] at hp ⊢
      by_contra hge
      apply hp
      push Not at hge
      have hX : X₀ ≤ ((p : ℕ) : ℝ) := le_trans (le_max_left _ _) hge
      have h2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := le_trans (le_max_right _ _) hge
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by linarith
      have hbound := hX₀ ((p : ℕ) : ℝ) hX
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hbound
      have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) := Real.log_pos (by linarith)
      have hrpos : 0 < ((p : ℕ) : ℝ) ^ t := Real.rpow_pos_of_pos hp0 t
      rw [abs_of_nonneg (Real.rpow_nonneg hlogpos.le 2),
        abs_of_nonneg hrpos.le] at hbound
      -- `log² p ≤ (1/4) p^t` forces the transported term above `1/p`
      rw [physical_transport_sq]
      have hlogsq : Real.log ((p : ℕ) : ℝ) ^ (2 : ℕ) = Real.log ((p : ℕ) : ℝ) ^ ((2 : ℝ)) := by
        rw [← Real.rpow_natCast (Real.log ((p : ℕ) : ℝ)) 2]
        norm_num
      have hlog2pos : (0 : ℝ) < Real.log ((p : ℕ) : ℝ) ^ (2 : ℕ) := by positivity
      calc 1 / ((p : ℕ) : ℝ) =
          (1 / (4 * ((p : ℕ) : ℝ))) * 4 := by field_simp
        _ ≤ primeActivationOccupancyFisherDensity p * 4 := by
            have := one_div_four_mul_le_primeActivationOccupancyFisherDensity p
            linarith
        _ ≤ primeActivationOccupancyFisherDensity p *
              (((p : ℕ) : ℝ) ^ t / Real.log ((p : ℕ) : ℝ) ^ (2 : ℕ)) := by
            have hFpos := primeActivationOccupancyFisherDensity_pos p
            have h4le : (4 : ℝ) ≤ ((p : ℕ) : ℝ) ^ t / Real.log ((p : ℕ) : ℝ) ^ (2 : ℕ) := by
              rw [le_div_iff₀ hlog2pos]
              rw [hlogsq]
              linarith
            exact mul_le_mul_of_nonneg_left h4le hFpos.le
        _ = ((p : ℕ) : ℝ) ^ t *
              (primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ 2) := by
            ring
    have hharm : Summable fun p : Nat.Primes => 1 / ((p : ℕ) : ℝ) := by
      refine summable_of_isBigO hsum ?_
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [hcof] with p hp
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((p : ℕ) : ℝ)),
        abs_of_nonneg (sq_nonneg _), one_mul]
      exact hp
    exact Nat.Primes.not_summable_one_div hharm
  · -- a nonpositive grade lands: `p^t ≤ 1` and the neutral energy converges
    intro ht
    have hbase := summable_fisher_fractional_logDomain (α := 0) (by norm_num)
    refine Summable.of_nonneg_of_le (f := fun p : Nat.Primes =>
      primeActivationOccupancyFisherDensity p /
        Real.log ((p : ℕ) : ℝ) ^ ((2 : ℝ) - 2 * 0)) (fun p => sq_nonneg _) (fun p => ?_) ?_
    · rw [physical_transport_sq]
      have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
      have hrle : ((p : ℕ) : ℝ) ^ t ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hp1 ht
      have hFpos := primeActivationOccupancyFisherDensity_pos p
      have hlogpos := log_prime_pos p
      have hquot : (0 : ℝ) ≤ primeActivationOccupancyFisherDensity p /
          Real.log ((p : ℕ) : ℝ) ^ 2 := by positivity
      calc ((p : ℕ) : ℝ) ^ t *
            (primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ 2) ≤
          1 * (primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hrle hquot
        _ = primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ 2 := one_mul _
        _ = primeActivationOccupancyFisherDensity p / Real.log ((p : ℕ) : ℝ) ^ ((2 : ℝ) - 2 * 0) := by
            rw [← Real.rpow_natCast (Real.log ((p : ℕ) : ℝ)) 2]
            norm_num
    · exact hbase

/-- **Two-orientation rigidity.**  Both orientations of the physical transport land exactly on
the critical grade. -/
theorem summable_both_orientations_iff (t : ℝ) :
    (Summable (fun p : Nat.Primes =>
        (((p : ℕ) : ℝ) ^ (t / 2) * routeRFisherLogPotential p) ^ 2) ∧
      Summable (fun p : Nat.Primes =>
        (((p : ℕ) : ℝ) ^ (-t / 2) * routeRFisherLogPotential p) ^ 2)) ↔ t = 0 := by
  rw [summable_physical_transport_sq_iff, summable_physical_transport_sq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    linarith
  · rintro rfl
    norm_num

/-! ## The `ℓ²` carrier and the exhaustion-free Cauchy criterion -/

/-- **Physical `ℓ²` membership at grade `t`.**  The transported potential is a genuine vector of
the fixed prime Hilbert carrier exactly on the nonpositive side. -/
theorem memℓp_two_physical_transport_iff (t : ℝ) :
    Memℓp (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (t / 2) * routeRFisherLogPotential p) 2 ↔
      t ≤ 0 := by
  rw [← summable_physical_transport_sq_iff t]
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  constructor <;> intro h
  · refine h.congr fun p => ?_
    rw [Real.norm_eq_abs, show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]
  · refine h.congr fun p => ?_
    rw [Real.norm_eq_abs, show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs]

/-- **Exhaustion-free Cauchy criterion.**  The net of finite-truncation energies over all finite
prime sets — which by coordinate orthogonality is the squared tail distance of the physical
truncation vectors along every exhaustion — is Cauchy exactly on the nonpositive side. -/
theorem cauchySeq_physical_truncation_iff (t : ℝ) :
    CauchySeq (fun S : Finset Nat.Primes =>
      ∑ p ∈ S, (((p : ℕ) : ℝ) ^ (t / 2) * routeRFisherLogPotential p) ^ 2) ↔ t ≤ 0 := by
  rw [← summable_physical_transport_sq_iff t, summable_iff_cauchySeq_finset]

/-! ## The exact Route R consequence -/

/-- **Xi-divisor classification.**  For every nonzero scalar — in particular for the
multiplicity-leading Xi Cartier coefficient — the physical coefficient field of a Xi divisor
point lies in the fixed `ℓ²` carrier exactly when the point is not in the right half-plane. -/
theorem memℓp_two_xiDivisor_coefficient_iff (c : ℂ) (hc : c ≠ 0) (ρ : XiDivisorSupport) :
    Memℓp (fun p : Nat.Primes =>
      c * (((p : ℕ) : ℝ) : ℂ) ^ ((ρ : ℂ) - 1 / 2) * (routeRFisherLogPotential p : ℂ)) 2 ↔
      (ρ : ℂ).re ≤ 1 / 2 := by
  have hkey : ∀ p : Nat.Primes,
      ‖c * (((p : ℕ) : ℝ) : ℂ) ^ ((ρ : ℂ) - 1 / 2) * (routeRFisherLogPotential p : ℂ)‖ ^
        ((2 : ℝ≥0∞).toReal) =
        ‖c‖ ^ 2 *
          ((((p : ℕ) : ℝ)) ^ ((2 * (ρ : ℂ).re - 1) / 2) * routeRFisherLogPotential p) ^ 2 := by
    intro p
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (routeRFisherLogPotential_nonneg p)]
    have hre : ((ρ : ℂ) - 1 / 2).re = (2 * (ρ : ℂ).re - 1) / 2 := by
      simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.one_im]
      norm_num
      ring
    rw [hre]
    ring
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  have hiff1 : (Summable fun p : Nat.Primes =>
      ‖c * (((p : ℕ) : ℝ) : ℂ) ^ ((ρ : ℂ) - 1 / 2) * (routeRFisherLogPotential p : ℂ)‖ ^
        ((2 : ℝ≥0∞).toReal)) ↔
      Summable fun p : Nat.Primes =>
        ‖c‖ ^ 2 * ((((p : ℕ) : ℝ)) ^ ((2 * (ρ : ℂ).re - 1) / 2) *
          routeRFisherLogPotential p) ^ 2 :=
    summable_congr hkey
  rw [hiff1]
  have hc2 : (‖c‖ ^ 2 : ℝ) ≠ 0 := by
    have := norm_pos_iff.mpr hc
    positivity
  rw [summable_mul_left_iff hc2, summable_physical_transport_sq_iff]
  constructor <;> intro h <;> linarith

end

end RHTower
