import GaloisForLFunctions.BezoutValuationIncidence.BlockEquidistributionSufficesForCrossScaleDispersion

/-!
# The reciprocity form of the Bernoulli kernel

With `ω = e^{2πi/d}` the nontrivial `d`-th roots are `ω^k`, `1 ≤ k < d`, and `|ω^k - 1|² = 4 sin²(πk/d)`.
The Fourier form `Φ_d(M) = Σ_{η ≠ 1} ηᴹ/|η - 1|²` becomes the cosine series

`Φ_d(M) = Σ_{k=1}^{d-1} cos(2πkM/d) / (4 sin²(πk/d))`.

Summing over `j` against `1/j²`, the Fourier series `Σ_{j ≥ 1} cos(2πjx)/j² = π² B₂(x)`,
`x ∈ [0, 1]`, turns the infinite Bernoulli kernel into a finite cosecant sum:

`𝔅(d, n) = Σ_{j ≥ 1} Φ_d(jn)/j² = (π²/4) Σ_{k=1}^{d-1} B₂({kn/d}) / sin²(πk/d)`.

For `n` prime to `d`, reindex by `k ↦ k n̄ mod d`, where `n n̄ ≡ 1 (mod d)`. The Bernoulli factor
then loses its dependence on `n` and the inverse moves into the cosecant:

`𝔅(d, n) = (π²/4) Σ_{k=1}^{d-1} B₂(k/d) / sin²(πk n̄/d)`.

This is the reciprocity `{N/pq} ↔ p̄/q + q̄/p` at second order. For primes `p < q`

`𝒢^{ec}(p, q) = ((p-1)/2 - log p) log q - p β_p + (π²/(4q)) Σ_{k=1}^{p-1} B₂(k/p) csc²(πk q̄/p) + O(¾ p³/q²)`.

So the fine cross-scale structure of the pronic Gram of two primes is a Dedekind-type
cosecant–Bernoulli sum in `q̄/p`. The bilinear form `Σ a_p b_q 𝒢^{ec}(p, q)` is then, beyond its rank
two, a bilinear form in the Kloosterman fractions `k q̄/p`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The second Bernoulli polynomial `B₂(x) = x² - x + 1/6`. -/
def bernoulliTwo (x : ℝ) : ℝ := x ^ 2 - x + 1 / 6

/-! ## §1. The Fourier series of `B₂` -/

/-- `Σ_{j ≥ 1} cos(2πjx)/j² = π² B₂(x)` for `x ∈ [0, 1]`. -/
theorem hasSum_cos_div_sq {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun j : ℕ => Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x) / ((j : ℝ) + 1) ^ 2)
      (Real.pi ^ 2 * bernoulliTwo x) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hB : Polynomial.eval x (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))) =
      bernoulliTwo x := by
    simp [Polynomial.bernoulli, Finset.sum_range_succ, bernoulli_one, bernoulli_zero,
      bernoulli_two, bernoulliTwo]
    ring
  have hval : (-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / ((2 * 1).factorial : ℕ) *
      bernoulliTwo x = Real.pi ^ 2 * bernoulliTwo x := by
    simp only [Nat.reduceAdd, Nat.reduceMul, Nat.factorial_two]
    push_cast
    ring
  rw [hB, hval] at h
  have h' := (hasSum_nat_add_iff' 1).mpr h
  have hf0 : ∑ i ∈ range 1, 1 / (i : ℝ) ^ (2 * 1) * Real.cos (2 * Real.pi * i * x) = 0 := by simp
  rw [hf0, sub_zero] at h'
  refine h'.congr_fun fun j => ?_
  push_cast
  ring

/-! ## §2. The nontrivial roots as powers of `ω` -/

/-- The standard primitive `d`-th root `ω = e^{2πi/d}`. -/
def stdRoot (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

theorem stdRoot_pow (d k : ℕ) :
    stdRoot d ^ k = Complex.exp (Complex.I * ((2 * Real.pi * k / d : ℝ) : ℂ)) := by
  rw [stdRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem nontrivialRoots_eq_image {d : ℕ} (hd : 0 < d) :
    nontrivialRoots d = (Ico 1 d).image (fun k => stdRoot d ^ k) := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hinj : Set.InjOn (fun k => stdRoot d ^ k) (Ico 1 d : Set ℕ) := fun i hi j hj h =>
    hω.pow_inj (Finset.mem_Ico.mp hi).2 (Finset.mem_Ico.mp hj).2 h
  symm
  refine eq_of_subset_of_card_le ?_ ?_
  · intro η hη
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hη
    have hk' := mem_Ico.mp hk
    refine (mem_nontrivialRoots hd).mpr ⟨fun h => ?_, by rw [← pow_mul, mul_comm, pow_mul,
      hω.pow_eq_one, one_pow]⟩
    have := (hω.pow_eq_one_iff_dvd k).mp h
    have := Nat.le_of_dvd (by omega) this
    omega
  · rw [card_nontrivialRoots hd, card_image_of_injOn hinj, Nat.card_Ico]

theorem norm_stdRoot_pow_sub_one_sq {d : ℕ} (k : ℕ) :
    ‖stdRoot d ^ k - 1‖ ^ 2 = 4 * Real.sin (Real.pi * k / d) ^ 2 := by
  rw [stdRoot_pow, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, sq_abs]
  ring_nf

theorem re_stdRoot_pow (d k : ℕ) :
    (stdRoot d ^ k).re = Real.cos (2 * Real.pi * k / d) := by
  rw [stdRoot_pow, Complex.exp_re]
  simp

/-- **Cosine form of the residue potential.** `Φ_d(M) = Σ_{k=1}^{d-1} cos(2πkM/d)/(4 sin²(πk/d))`. -/
theorem residuePotential_eq_cos {d : ℕ} (hd : 0 < d) (M : ℕ) :
    residuePotential d M =
      ∑ k ∈ Ico 1 d, Real.cos (2 * Real.pi * (k * M : ℕ) / d) / (4 * Real.sin (Real.pi * k / d) ^ 2) := by
  have hω : IsPrimitiveRoot (stdRoot d) d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hinj : Set.InjOn (fun k => stdRoot d ^ k) (Ico 1 d : Set ℕ) := fun i hi j hj h =>
    hω.pow_inj (Finset.mem_Ico.mp hi).2 (Finset.mem_Ico.mp hj).2 h
  have h := residuePotential_eq_spectral hd M
  rw [nontrivialRoots_eq_image hd, sum_image hinj] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  refine sum_congr rfl fun k _ => ?_
  rw [Complex.re_ofReal_mul, ← pow_mul, re_stdRoot_pow, norm_stdRoot_pow_sub_one_sq]
  ring

/-! ## §3. The finite Fourier form of the Bernoulli kernel -/

/-- **Finite Fourier form.** `𝔅(d, n) = (π²/4) Σ_{k=1}^{d-1} B₂({kn/d})/sin²(πk/d)`. -/
theorem bernoulliKernel_eq_finite {d : ℕ} (hd : 0 < d) (n : ℕ) :
    bernoulliKernel d n = Real.pi ^ 2 / 4 *
      ∑ k ∈ Ico 1 d, bernoulliTwo (((k * n % d : ℕ) : ℝ) / d) / Real.sin (Real.pi * k / d) ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hk : ∀ k ∈ Ico 1 d, HasSum
      (fun j : ℕ => Real.cos (2 * Real.pi * (k * ((j + 1) * n) : ℕ) / d) /
        (4 * Real.sin (Real.pi * k / d) ^ 2) / ((j : ℝ) + 1) ^ 2)
      (Real.pi ^ 2 * bernoulliTwo (((k * n % d : ℕ) : ℝ) / d) /
        (4 * Real.sin (Real.pi * k / d) ^ 2)) := by
    intro k _
    set x : ℝ := ((k * n % d : ℕ) : ℝ) / d
    have hx : x ∈ Set.Icc (0 : ℝ) 1 := by
      have hlt : ((k * n % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt _ hd
      exact ⟨by positivity, by rw [div_le_one hdR]; exact hlt.le⟩
    have hs := (hasSum_cos_div_sq hx).div_const (4 * Real.sin (Real.pi * k / d) ^ 2)
    refine hs.congr_fun fun j => ?_
    -- reduce the phase modulo one
    have hphase : Real.cos (2 * Real.pi * (k * ((j + 1) * n) : ℕ) / d) =
        Real.cos (2 * Real.pi * ((j : ℝ) + 1) * x) := by
      have hdiv := Nat.div_add_mod (k * n) d
      have hcast : ((k * ((j + 1) * n) : ℕ) : ℝ) = ((j : ℝ) + 1) * (d * ((k * n / d : ℕ) : ℝ)) +
          ((j : ℝ) + 1) * ((k * n % d : ℕ) : ℝ) := by
        have : ((k * n : ℕ) : ℝ) = d * ((k * n / d : ℕ) : ℝ) + ((k * n % d : ℕ) : ℝ) := by
          exact_mod_cast hdiv.symm
        push_cast at this ⊢
        rw [show (k : ℝ) * (((j : ℝ) + 1) * n) = ((j : ℝ) + 1) * ((k : ℝ) * n) by ring, this]
        ring
      rw [hcast]
      have hper : 2 * Real.pi * (((j : ℝ) + 1) * (d * ((k * n / d : ℕ) : ℝ)) +
          ((j : ℝ) + 1) * ((k * n % d : ℕ) : ℝ)) / d =
          2 * Real.pi * ((j : ℝ) + 1) * x + (((j + 1) * (k * n / d) : ℕ) : ℝ) * (2 * Real.pi) := by
        simp only [x]
        push_cast
        field_simp
        ring
      rw [hper, Real.cos_add_nat_mul_two_pi]
    rw [hphase]
    ring
  have hsum := hasSum_sum hk
  have hB := hasSum_bernoulliKernel hd n
  have heq : (fun j : ℕ => ∑ k ∈ Ico 1 d, Real.cos (2 * Real.pi * (k * ((j + 1) * n) : ℕ) / d) /
      (4 * Real.sin (Real.pi * k / d) ^ 2) / ((j : ℝ) + 1) ^ 2) =
      fun j : ℕ => residuePotential d ((j + 1) * n) / ((j : ℝ) + 1) ^ 2 := by
    ext j
    rw [residuePotential_eq_cos hd, sum_div]
  rw [heq] at hsum
  rw [hB.unique hsum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  ring

/-! ## §4. The reciprocity form -/

theorem sin_sq_mod {d : ℕ} (hd : 0 < d) (m : ℕ) :
    Real.sin (Real.pi * (m % d : ℕ) / d) ^ 2 = Real.sin (Real.pi * m / d) ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdiv := Nat.div_add_mod m d
  have hm : (m : ℝ) = d * ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) := by exact_mod_cast hdiv.symm
  have hphase : Real.pi * m / d = Real.pi * (m % d : ℕ) / d + ((m / d : ℕ) : ℝ) * Real.pi := by
    rw [hm]; field_simp; ring
  conv_rhs => rw [hphase, Real.sin_add_nat_mul_pi]
  rw [mul_pow, ← pow_mul, mul_comm (m / d) 2, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **The reciprocity form of the Bernoulli kernel.** If `n n̄ ≡ 1 (mod d)`, `d ≥ 2`, then
`𝔅(d, n) = (π²/4) Σ_{k=1}^{d-1} B₂(k/d)/sin²(πk n̄/d)`. -/
theorem bernoulliKernel_eq_reciprocity {d n nbar : ℕ} (hd : 2 ≤ d) (hn : n * nbar % d = 1) :
    bernoulliKernel d n = Real.pi ^ 2 / 4 *
      ∑ k ∈ Ico 1 d, bernoulliTwo ((k : ℝ) / d) / Real.sin (Real.pi * (k * nbar : ℕ) / d) ^ 2 := by
  have hd0 : 0 < d := by omega
  rw [bernoulliKernel_eq_finite hd0]
  congr 1
  -- reindex `k = k' n̄ mod d`
  refine sum_nbij' (fun k => k * n % d) (fun k' => k' * nbar % d) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := mem_Ico.mp hk
    refine mem_Ico.mpr ⟨?_, Nat.mod_lt _ hd0⟩
    by_contra h0
    have h0' : k * n % d = 0 := by omega
    have : k % d = 0 := by
      have h1 : k * n * nbar % d = 0 := by rw [Nat.mul_mod, h0', zero_mul, Nat.zero_mod]
      have h2 : k * n * nbar % d = k % d := by
        rw [mul_assoc, Nat.mul_mod, hn, mul_one, Nat.mod_mod]
      omega
    rw [Nat.mod_eq_of_lt hk'.2] at this
    omega
  · intro k hk
    have hk' := mem_Ico.mp hk
    refine mem_Ico.mpr ⟨?_, Nat.mod_lt _ hd0⟩
    by_contra h0
    have h0' : k * nbar % d = 0 := by omega
    have : k % d = 0 := by
      have h1 : k * nbar * n % d = 0 := by rw [Nat.mul_mod, h0', zero_mul, Nat.zero_mod]
      have h2 : k * nbar * n % d = k % d := by
        rw [mul_assoc, mul_comm nbar n, Nat.mul_mod, hn, mul_one, Nat.mod_mod]
      omega
    rw [Nat.mod_eq_of_lt hk'.2] at this
    omega
  · intro k hk
    have hk' := mem_Ico.mp hk
    show k * n % d * nbar % d = k
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, Nat.mul_mod, hn, mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt hk'.2]
  · intro k hk
    have hk' := mem_Ico.mp hk
    show k * nbar % d * n % d = k
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, mul_comm nbar n, Nat.mul_mod, hn,
      mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hk'.2]
  · intro k hk
    have hk' := mem_Ico.mp hk
    have hmod : k * n % d * nbar % d = k := by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_assoc, Nat.mul_mod, hn, mul_one, Nat.mod_mod,
        Nat.mod_eq_of_lt hk'.2]
    rw [← sin_sq_mod hd0 (k * n % d * nbar), hmod]

/-! ## §5. Two primes through the reciprocity -/

/-- **The pronic Gram of two primes in `q̄/p`.** For primes `p, q ≤ N` and `q q̄ ≡ 1 (mod p)`,
`|𝒢^{ec}(p, q) - D_p log q + p β_p - (π²/(4q)) Σ_{k=1}^{p-1} B₂(k/p) csc²(πk q̄/p)| ≤ ¾ p³/q²`. -/
theorem abs_pmRamanujanEnergyCenteredGram_sub_reciprocity_le {N p q qbar : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpN : p ≤ N) (hqN : q ≤ N) (hqbar : q * qbar % p = 1) :
    |pmRamanujanEnergyCenteredGram p q - (((p : ℝ) - 1) / 2 - Real.log p) * Real.log q +
        p * rowBeta N (unitRow p) - Real.pi ^ 2 / (4 * q) *
          ∑ k ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) / Real.sin (Real.pi * (k * qbar : ℕ) / p) ^ 2| ≤
      3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have h := abs_pmRamanujanEnergyCenteredGram_sub_second_order_le hp hq hpN hqN
  rw [bernoulliKernel_eq_reciprocity hp.two_le hqbar] at h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  convert h using 3
  field_simp

/-- For distinct primes the inverse exists, so the reciprocity form always applies. -/
theorem exists_reciprocity_form {N p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpN : p ≤ N) (hqN : q ≤ N) :
    ∃ qbar : ℕ, q * qbar % p = 1 ∧
      |pmRamanujanEnergyCenteredGram p q - (((p : ℝ) - 1) / 2 - Real.log p) * Real.log q +
          p * rowBeta N (unitRow p) - Real.pi ^ 2 / (4 * q) *
            ∑ k ∈ Ico 1 p, bernoulliTwo ((k : ℝ) / p) / Real.sin (Real.pi * (k * qbar : ℕ) / p) ^ 2| ≤
        3 / 4 * (p : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  obtain ⟨qbar, -, hqbar⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  exact ⟨qbar, hqbar, abs_pmRamanujanEnergyCenteredGram_sub_reciprocity_le hp hq hpN hqN hqbar⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
