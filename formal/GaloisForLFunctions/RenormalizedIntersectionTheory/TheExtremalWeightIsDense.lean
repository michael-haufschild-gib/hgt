import GaloisForLFunctions.RenormalizedIntersectionTheory.TheGlobalPoleIsTheExtremalWeight
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# The extremal weight is dense over the integers

On the `S`-units the archimedean pole is the extremal weight `χ^∅ = ∏_{p∈S} χ_p⁻¹`
(`TheGlobalPoleIsTheExtremalWeight`). Its **exponents** `log |u|` record the dilation factor of the
boost. This file compares their value group over one prime and over two.

* **One prime: quantized** (`not_dense_exponents_single`): on the `p`-units the exponents form the
  lattice `(log p) ℤ`.
* **Function fields: quantized** (`not_dense_exponents_of_quantized`): when all place sizes are
  integer multiples of one size — over `𝔽_q[T]` the place `P` has size `deg P · log q` — the
  exponents of every `S`-unit group lie in a lattice; Frobenius is the generator.
* **Two primes: dense** (`irrational_log_div_log`, `dense_exponents_pair`): `log p / log q` is
  irrational for distinct primes, so the exponents `a log p + b log q` are dense in `ℝ`.
* **The archimedean boost reads the exponents** (`log_norm_archBoost_sUnit`):
  `log ‖χ_∞(∏ q^{n_q})‖ = ½ Σ n_q log q`.

So the product formula identifies the archimedean factor with a dense subgroup of `ℝ_{>0}` as soon as
two primes are present: what separates `ℤ` from `𝔽_q[T]` in the extremal weight is density of the
conformal factor, not its existence. Continuity at the real place (dense values) is exactly what the
Haar and Hecke-supported carriers cannot match at finite index
(`AdelicKreinGeometry.ArchimedeanContinuityAgainstHeightDecay`).
-/

open Finset Set

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- **Distinct primes have incommensurable logarithms.** -/
theorem irrational_log_div_log {p q : Nat.Primes} (hpq : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  rintro ⟨r, hr⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast q.2.one_lt
  have hlp := Real.log_pos hp1
  have hlq := Real.log_pos hq1
  have hrpos : (0 : ℝ) < r := by rw [hr]; exact div_pos hlp hlq
  have hnum : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hrpos)
  -- `den · log p = num · log q`, hence `p^den = q^num`
  have hcast : (r : ℝ) = (r.num : ℝ) / r.den := by
    rw [Rat.cast_def]
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hrel : (r.den : ℝ) * Real.log p = (r.num.toNat : ℝ) * Real.log q := by
    have hnn : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnum.le
    rw [hnn]
    have := hr.symm.trans hcast
    field_simp at this
    linarith
  have hpow : ((p : ℕ) ^ r.den : ℕ) = (q : ℕ) ^ r.num.toNat := by
    have h := congrArg Real.exp hrel
    rw [← Real.log_pow, ← Real.log_pow, Real.exp_log (by positivity),
      Real.exp_log (by positivity)] at h
    exact_mod_cast h
  have hdvd : (p : ℕ) ∣ (q : ℕ) ^ r.num.toNat := by
    rw [← hpow]; exact dvd_pow_self _ r.den_pos.ne'
  exact hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp (p.2.dvd_of_dvd_pow hdvd)))

/-- **Two primes: the exponents are dense.** -/
theorem dense_exponents_pair {p q : Nat.Primes} (hpq : p ≠ q) :
    Dense (Set.range fun n : ℤ × ℤ => (n.1 : ℝ) * Real.log p + n.2 * Real.log q) := by
  have hd := dense_addSubgroupClosure_pair_iff.mpr (irrational_log_div_log hpq)
  refine hd.mono ?_
  intro x hx
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.mp hx
  exact ⟨(m, n), by simp [zsmul_eq_mul]⟩

/-- **One prime: the exponents are quantized.** -/
theorem not_dense_exponents_single (p : Nat.Primes) :
    ¬ Dense (Set.range fun n : ℤ => (n : ℝ) * Real.log p) := by
  have h := not_denseRange_zsmul (a := Real.log p)
  simpa [DenseRange, zsmul_eq_mul] using h

/-- **Commensurable sizes are quantized.** If every place has size `d_v · c` with `d_v ∈ ℤ` — as over
`𝔽_q[T]`, where the place `P` has size `deg P · log q` — the exponents `Σ n_v d_v c` of the
`S`-units lie in `c ℤ` and are not dense. -/
theorem not_dense_exponents_of_quantized {ι : Type*} (S : Finset ι) (d : ι → ℤ) (c : ℝ) :
    ¬ Dense (Set.range fun n : ι → ℤ => ∑ v ∈ S, (n v : ℝ) * (d v * c)) := by
  intro hd
  refine not_denseRange_zsmul (a := c) (hd.mono ?_)
  rintro _ ⟨n, rfl⟩
  refine ⟨∑ v ∈ S, n v * d v, ?_⟩
  simp only [zsmul_eq_mul, Int.cast_sum, Int.cast_mul, sum_mul]
  exact sum_congr rfl fun v _ => by ring

/-- **The archimedean boost reads the exponents** on the `S`-units. -/
theorem log_norm_archBoost_sUnit (S : Finset Nat.Primes) (n : Nat.Primes → ℤ) :
    Real.log ‖archBoost (sUnit S n)‖ = (1 / 2) * ∑ q ∈ S, (n q : ℝ) * Real.log q := by
  rw [sUnit, map_prod, norm_prod, Real.log_prod (fun q _ => by
    rw [map_zpow, norm_zpow, archBoost_primeUnit, Complex.norm_real]
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr q.2.pos) _).ne')), mul_sum]
  refine sum_congr rfl fun q _ => ?_
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr q.2.pos
  rw [map_zpow, norm_zpow, archBoost_primeUnit, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hq0.le _), Real.log_zpow, Real.log_rpow hq0]
  ring

end GaloisForLFunctions.RenormalizedIntersectionTheory
