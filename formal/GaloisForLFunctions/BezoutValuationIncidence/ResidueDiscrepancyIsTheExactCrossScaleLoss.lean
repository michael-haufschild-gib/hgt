import GaloisForLFunctions.BezoutValuationIncidence.TypeIIBarrierSurvivesTheRankTwoSideConditions

/-!
# The residue discrepancy is the exact cross-scale loss

**Residue averages.** In the Fourier form `Φ_d(M) = Σ_{η ∈ T_d} η^M/|η - 1|²`, summing `η^{jr}` over
`r < d` keeps exactly the roots with `η^j = 1`. These are the nontrivial `g`-th roots, `g = gcd(j, d)`.
Hence

`Σ_{r < d} Φ_d(jr) = d Φ_g(0) = d (gcd(j, d)² - 1)/12`.

For a prime `p` only the multiples `j ≡ 0 (mod p)` contribute to the Bernoulli kernel, and

`Σ_{r < p} 𝔅(p, r) = π²(p² - 1)/(72 p)`.

The average of the kernel over residues is `π²(p² - 1)/(72 p²) < π²/72`, smaller by the factor `p²`
than its maximum `𝔅(p, 0) = π²(p² - 1)/72`.

**The discrepancy law.** Let `ρ(p, r) = Σ_{n ≡ r (p)} c'(n)/n²`, `S' = Σ_n c'(n)/n²`, and let
`Δ_p(c') = Σ_{r < p} |ρ(p, r) - S'/p|` be the `ℓ¹` residue discrepancy. Then for every row `c` on primes

`|B + m R' + β H' - (π²/72) S' Σ_p c(p)(p² - 1)/p³|
  ≤ (π²/72) Σ_p |c(p)| ((p² - 1)/p) Δ_p(c') + ¾ Σ_p |c(p)| p² Σ_n |c'(n)|/n³`.

The cross-scale remainder at one modulus is exactly the residue discrepancy of the large-scale weighted
row modulo the small primes, at the rate `π²/72` per unit of discrepancy. The equidistributed part costs
only `(π²/72)|S'| Σ_p |c(p)|/p`, a gain of `p²` over the rank-two size. The rate is attained: a large
scale concentrated on one class has `Δ_p = 2 S'(1 - 1/p)`, and coherent windows and the Bézout seeds
`q ≡ 1 (mod p)` realise the matching lower bounds. Type-II dispersion beyond `θ = 1` at a single modulus
is therefore equivalent to `Σ_p |a_p| p Δ_p(c') = o(Σ_p |a_p| p S')`: weighted `ℓ¹` equidistribution
of the large-scale coefficients in residue classes to the small prime moduli.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Residue averages of the potential and of the kernel -/

/-- The nontrivial `d`-th roots with `η^j = 1` are the nontrivial `gcd(j, d)`-th roots. -/
theorem nontrivialRoots_filter_pow_eq_one {d : ℕ} (hd : 0 < d) (j : ℕ) :
    (nontrivialRoots d).filter (fun η => η ^ j = 1) = nontrivialRoots (Nat.gcd j d) := by
  have hg : 0 < Nat.gcd j d := Nat.gcd_pos_of_pos_right j hd
  ext η
  rw [mem_filter, mem_nontrivialRoots hd, mem_nontrivialRoots hg]
  constructor
  · rintro ⟨⟨h1, hd'⟩, hj⟩
    exact ⟨h1, pow_gcd_eq_one.mpr ⟨hj, hd'⟩⟩
  · rintro ⟨h1, hg'⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · obtain ⟨k, hk⟩ := Nat.gcd_dvd_right j d
      rw [hk, pow_mul, hg', one_pow]
    · obtain ⟨k, hk⟩ := Nat.gcd_dvd_left j d
      rw [hk, pow_mul, hg', one_pow]

/-- **Residue average of the potential.** `Σ_{r < d} Φ_d(jr) = d (gcd(j, d)² - 1)/12`. -/
theorem sum_range_residuePotential_mul {d : ℕ} (hd : 0 < d) (j : ℕ) :
    ∑ r ∈ range d, residuePotential d (j * r) = d * (((Nat.gcd j d : ℕ) : ℝ) ^ 2 - 1) / 12 := by
  set g := Nat.gcd j d
  have hg : 0 < g := Nat.gcd_pos_of_pos_right j hd
  set w : ℂ → ℂ := fun η => (((‖η - 1‖ ^ 2)⁻¹ : ℝ) : ℂ)
  have hgeom : ∀ η ∈ nontrivialRoots d,
      ∑ r ∈ range d, η ^ (j * r) = if η ^ j = 1 then (d : ℂ) else 0 := by
    intro η hη
    have hηd := ((mem_nontrivialRoots hd).mp hη).2
    simp_rw [pow_mul]
    split_ifs with h
    · simp [h]
    · have hpow : (η ^ j) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, hηd, one_pow]
      rw [geom_sum_eq h, hpow, sub_self, zero_div]
  have hC : ((∑ r ∈ range d, residuePotential d (j * r) : ℝ) : ℂ) =
      ((residuePotential g 0 : ℝ) : ℂ) * (d : ℂ) := by
    calc ((∑ r ∈ range d, residuePotential d (j * r) : ℝ) : ℂ)
        = ∑ r ∈ range d, ∑ η ∈ nontrivialRoots d, w η * η ^ (j * r) := by
          push_cast
          exact sum_congr rfl fun r _ => residuePotential_eq_spectral hd _
      _ = ∑ η ∈ nontrivialRoots d, w η * ∑ r ∈ range d, η ^ (j * r) := by
          rw [sum_comm]
          exact sum_congr rfl fun η _ => by rw [mul_sum]
      _ = ∑ η ∈ nontrivialRoots d, if η ^ j = 1 then w η * d else 0 :=
          sum_congr rfl fun η hη => by rw [hgeom η hη]; split_ifs <;> simp
      _ = (∑ η ∈ nontrivialRoots g, w η) * d := by
          rw [← sum_filter, nontrivialRoots_filter_pow_eq_one hd, sum_mul]
      _ = ((residuePotential g 0 : ℝ) : ℂ) * (d : ℂ) := by
          rw [residuePotential_eq_spectral hg 0]
          simp [w]
  have hR : ∑ r ∈ range d, residuePotential d (j * r) = residuePotential g 0 * d := by
    exact_mod_cast hC
  rw [hR]
  simp [residuePotential]
  ring

/-- **Residue average of the kernel at a prime.** `Σ_{r < p} 𝔅(p, r) = π²(p² - 1)/(72 p)`. -/
theorem sum_range_bernoulliKernel_prime {p : ℕ} (hp : p.Prime) :
    ∑ r ∈ range p, bernoulliKernel p r = Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * p) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  set C : ℝ := p * ((p : ℝ) ^ 2 - 1) / 12
  have hsum := hasSum_sum (s := range p) fun r _ => hasSum_bernoulliKernel hp0 r
  have hterm : ∀ j : ℕ, ∑ r ∈ range p, residuePotential p ((j + 1) * r) / ((j : ℝ) + 1) ^ 2 =
      if p ∣ j + 1 then C / ((j : ℝ) + 1) ^ 2 else 0 := by
    intro j
    rw [← sum_div, sum_range_residuePotential_mul hp0]
    split_ifs with h
    · rw [Nat.gcd_eq_right h]
    · have hcop : Nat.gcd (j + 1) p = 1 :=
        Nat.Coprime.gcd_eq_one ((hp.coprime_iff_not_dvd.mpr h).symm)
      rw [hcop]; simp
  simp_rw [hterm] at hsum
  -- the multiples of `p`
  set g : ℕ → ℕ := fun k => p * (k + 1) - 1
  have hg1 : ∀ k, g k + 1 = p * (k + 1) := fun k =>
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hginj : Function.Injective g := fun a b h => by
    have ha := hg1 a
    have hb := hg1 b
    have : p * (a + 1) = p * (b + 1) := by rw [← ha, ← hb, h]
    have := Nat.eq_of_mul_eq_mul_left hp0 this
    omega
  have hrange : ∀ x ∉ Set.range g,
      (if p ∣ x + 1 then C / ((x : ℝ) + 1) ^ 2 else 0) = 0 := by
    intro x hx
    rw [if_neg]
    rintro ⟨m, hm⟩
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hm
      · omega
    refine hx ⟨m - 1, ?_⟩
    simp only [g]
    rw [Nat.sub_add_cancel hm1, ← hm]
    omega
  have hz : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hcomp : HasSum ((fun x : ℕ => if p ∣ x + 1 then C / ((x : ℝ) + 1) ^ 2 else 0) ∘ g)
      (C / (p : ℝ) ^ 2 * (Real.pi ^ 2 / 6)) := by
    refine (hz.mul_left (C / (p : ℝ) ^ 2)).congr_fun fun k => ?_
    have hdvd : p ∣ g k + 1 := ⟨k + 1, hg1 k⟩
    have hcast : ((g k : ℕ) : ℝ) + 1 = (p : ℝ) * ((k : ℝ) + 1) := by exact_mod_cast hg1 k
    simp only [Function.comp, if_pos hdvd, hcast]
    field_simp
  have hfull := (hginj.hasSum_iff hrange).mp hcomp
  rw [hsum.unique hfull]
  simp only [C]
  field_simp
  ring

/-! ## §2. The discrepancy law -/

/-- The `ℓ¹` residue discrepancy `Δ_d(c') = Σ_{r < d} |ρ(d, r) - S'/d|`, `S' = Σ_n c'(n)/n²`. -/
def residueDiscrepancy (N : ℕ) (c' : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ range d, |residueMass N c' d r - (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) / d|

/-- **One prime modulus.** `|Σ_n c'(n) 𝔅(p, n)/n² - (π²(p² - 1)/(72p²)) S'| ≤ (π²(p² - 1)/72) Δ_p(c')`. -/
theorem abs_sum_mul_bernoulliKernel_sub_mean_le {p : ℕ} (hp : p.Prime) (N : ℕ) (c' : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, c' n * (bernoulliKernel p n / (n : ℝ) ^ 2) -
        Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2| ≤
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' p := by
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [sum_mul_bernoulliKernel_eq_residueMass hp.pos]
  have hsplit : ∑ r ∈ range p, bernoulliKernel p r * residueMass N c' p r -
      Real.pi ^ 2 * ((p : ℝ) ^ 2 - 1) / (72 * (p : ℝ) ^ 2) * S' =
      ∑ r ∈ range p, bernoulliKernel p r * (residueMass N c' p r - S' / p) := by
    have e : ∑ r ∈ range p, bernoulliKernel p r * (residueMass N c' p r - S' / p) =
        ∑ r ∈ range p, bernoulliKernel p r * residueMass N c' p r -
          (∑ r ∈ range p, bernoulliKernel p r) * (S' / p) := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun r _ => by ring
    rw [e, sum_range_bernoulliKernel_prime hp]
    field_simp
  rw [hsplit, residueDiscrepancy, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_bernoulliKernel_le_sharp hp.two_le r) (abs_nonneg _)

/-- **The discrepancy law.** For every row `c` on primes and every large-scale row `c'`,
`|B + m R' + β H' - (π²/72) S' Σ_p c(p)(p² - 1)/p³|
  ≤ (π²/72) Σ_p |c(p)| ((p² - 1)/p) Δ_p(c') + ¾ Σ_d |c(d)| d² Σ_n |c'(n)|/n³`. -/
theorem abs_rowBilinear_add_mean_add_beta_sub_equidistributed_le (N : ℕ) {c c' : ℕ → ℝ}
    (hc : ∀ d, c d ≠ 0 → d.Prime) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' -
        Real.pi ^ 2 / 72 * (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) *
          ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3| ≤
      Real.pi ^ 2 / 72 * ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_bernoulli_le N c c'
  set E := rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c'
  set K := ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) * (bernoulliKernel d n / (n : ℝ) ^ 2)
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hK : K = ∑ d ∈ Icc 1 N, c d / d * ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2) := by
    simp only [K]
    rw [sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hmain : |K - Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3| ≤
      Real.pi ^ 2 / 72 *
        ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d := by
    have e1 : Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3 =
        ∑ d ∈ Icc 1 N, Real.pi ^ 2 / 72 * S' * (c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3) :=
      mul_sum _ _ _
    have e2 : Real.pi ^ 2 / 72 *
        ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d =
        ∑ d ∈ Icc 1 N, Real.pi ^ 2 / 72 *
          (|c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d) := mul_sum _ _ _
    rw [hK, e1, ← sum_sub_distrib, e2]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
    by_cases hcd : c d = 0
    · simp [hcd]
    have hp := hc d hcd
    have h := abs_sum_mul_bernoulliKernel_sub_mean_le hp N c'
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hp.pos
    set X := ∑ n ∈ Icc 1 N, c' n * (bernoulliKernel d n / (n : ℝ) ^ 2)
    have e : c d / d * X - Real.pi ^ 2 / 72 * S' * (c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3) =
        c d / d * (X - Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / (72 * (d : ℝ) ^ 2) * S') := by
      field_simp
    rw [e, abs_mul, abs_div, abs_of_pos hd0]
    calc |c d| / d * |X - Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / (72 * (d : ℝ) ^ 2) * S'|
        ≤ |c d| / d * (Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / 72 * residueDiscrepancy N c' d) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = Real.pi ^ 2 / 72 * (|c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d) := by
          field_simp
  calc |E - Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3|
      ≤ |E - K| + |K - Real.pi ^ 2 / 72 * S' * ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3| :=
        abs_sub_le _ _ _
    _ ≤ 3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 3 +
          Real.pi ^ 2 / 72 *
            ∑ d ∈ Icc 1 N, |c d| * (((d : ℝ) ^ 2 - 1) / d) * residueDiscrepancy N c' d :=
        add_le_add hlaw hmain
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
