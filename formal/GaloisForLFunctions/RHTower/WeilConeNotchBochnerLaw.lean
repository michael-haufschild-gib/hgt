import GaloisForLFunctions.RHTower.WeilConeHarmonicPinning

/-!
# The notch Bochner law: the complete notch information of a Weil deviation

Let `lam` be full-cone Weil-positive with notch-small deviation `d = lam − Λ`. Fix a finite set `P` of
primes. For an exponent vector `h ∈ ℕ^P` write `P^h = Π_p p^{h_p}` and
`gcd(n, P^h) = Π_p p^{min(v_p(n), h_p)}` (`gcdPart`), and
`Γ(g) = Σ_n d(n) gcd(n, P^{g⁺})/n` for `g ∈ ℤ^P` (`gcdHarmonicSum`).

**Theorem** (`notchBochner_le`). For every finite `A ⊂ ℤ^P` and real coefficients `c`, if every `Γ`
converges, then
`Σ_{a,a'∈A} c_a c_{a'} (P^{|a−a'|})^{−1/2} Γ(a − a') ≤ 0`.

So `g ↦ (P^{|g|})^{−1/2} Γ(g)` is negative definite on the lattice `ℤ^P`. This is the whole content of
the notch tests: the twist `|Σ_a c_a e^{iτλ(a)}|²` has fibre sums exactly
`Σ_{a,a'} c_a c_{a'} (P^{|a−a'|})^{−1/2} Γ_k(a − a')` (`sum_twistFibre_eq`). The value at `g = 0` is
the harmonic constant `T = Σ_n d(n)/n`. By Bochner's theorem the notch information is therefore a
positive measure of total mass `−T` on the torus `(ℝ/ℤ)^P`. With `T = 0` it vanishes, which is harmonic
pinning (MUST-619). With `T < 0` every such measure is allowed.

**Proof.** `twistNorm(n, g) · gcd(n, P^{g⁺})² = n · P^{g⁺} · P^{g⁻}`, from the exponent identity
`|v − g| + 2 min(v, g⁺) = v + |g|` (`twistNorm_mul_gcdPart_sq`). Hence the main weight is
`n^{−1/2} Σ_{a,a'} c_a c_{a'} gcd(n, P^{(a−a')⁺}) (P^{|a−a'|})^{−1/2}`. A positive limit of the fibre
sums contradicts the fibre Bochner law (MUST-606).
-/

noncomputable section

open Filter Topology RHTower

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable
open RHTower.PrimeSmallDeviation

variable {P : Finset ℕ}

/-- `gcd(n, P^h) = Π_{p∈P} p^{min(v_p(n), h_p)}`. -/
def gcdPart (P : Finset ℕ) (n : ℕ) (h : P → ℕ) : ℕ :=
  ∏ p : P, (p : ℕ) ^ min (n.factorization p) (h p)

theorem gcdPart_pos (hP : ∀ p ∈ P, p.Prime) (n : ℕ) (h : P → ℕ) : 0 < gcdPart P n h :=
  Finset.prod_pos fun p _ => pow_pos (hP p p.2).pos _

/-- `twistNorm(n, g) · gcd(n, P^{g⁺})² = n · P^{g⁺} · P^{g⁻}`. -/
theorem twistNorm_mul_gcdPart_sq {n : ℕ} (hn : n ≠ 0) (g : P → ℤ) :
    twistNorm P n g * (gcdPart P n (fun p => (g p).toNat) : ℝ) ^ 2 =
      n * ((vecNum g * vecDen g : ℕ) : ℝ) := by
  rw [twistNorm_eq_mul_prod, vecNum_mul_vecDen_eq_prod]
  have key : (∏ p : P, (p : ℕ) ^ (vecOf P n p - g p).natAbs) *
      (gcdPart P n (fun p => (g p).toNat)) ^ 2 =
      smoothPart P n * ∏ p : P, (p : ℕ) ^ (g p).natAbs := by
    unfold gcdPart smoothPart
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    simp only [vecOf]
    omega
  have h2 : (roughPart P n * ∏ p : P, (p : ℕ) ^ (vecOf P n p - g p).natAbs) *
      (gcdPart P n (fun p => (g p).toNat)) ^ 2 = n * ∏ p : P, (p : ℕ) ^ (g p).natAbs := by
    rw [mul_assoc, key, ← mul_assoc, mul_comm (roughPart _ _), smoothPart_mul_roughPart n hn]
  exact_mod_cast h2

/-- The Gram weight `(P^{|g|})^{−1/2} = (P^{g⁺} P^{g⁻})^{−1/2}`. -/
def twistGramWeight (g : P → ℤ) : ℝ := (Real.sqrt ((vecNum g * vecDen g : ℕ) : ℝ))⁻¹

/-- `twistNorm(n, g)^{−1/2} = gcd(n, P^{g⁺}) n^{−1/2} (P^{|g|})^{−1/2}`. -/
theorem inv_sqrt_twistNorm_eq_gcdPart (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0)
    (g : P → ℤ) :
    (Real.sqrt (twistNorm P n g))⁻¹ =
      (gcdPart P n (fun p => (g p).toNat) : ℝ) * (Real.sqrt n)⁻¹ * twistGramWeight g := by
  have hG : (0 : ℝ) < gcdPart P n (fun p => (g p).toNat) := by
    exact_mod_cast gcdPart_pos hP n _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hV : (0 : ℝ) < ((vecNum g * vecDen g : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (vecNum_pos hP g) (vecDen_pos hP g)
  have ht : twistNorm P n g = n * ((vecNum g * vecDen g : ℕ) : ℝ) /
      (gcdPart P n (fun p => (g p).toNat) : ℝ) ^ 2 := by
    rw [eq_div_iff (by positivity)]; exact twistNorm_mul_gcdPart_sq hn g
  unfold twistGramWeight
  rw [ht, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hG.le, Real.sqrt_mul hn0.le, inv_div]
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsV : 0 < Real.sqrt ((vecNum g * vecDen g : ℕ) : ℝ) := Real.sqrt_pos.mpr hV
  field_simp

/-- **The main weight of a twist polynomial in gcd form.** -/
theorem twistMainWeight_eq_gcd (hP : ∀ p ∈ P, p.Prime) (A : Finset (P → ℤ))
    (c : (P → ℤ) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    twistMainWeight P A c n = (Real.sqrt n)⁻¹ * ∑ a ∈ A, ∑ a' ∈ A, c a * c a' *
      twistGramWeight (a - a') * (gcdPart P n (fun p => ((a - a') p).toNat) : ℝ) := by
  unfold twistMainWeight
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [inv_sqrt_twistNorm_eq_gcdPart hP hn]
  ring

/-- `Γ_k(g) = Σ_{n≤k} d(n) gcd(n, P^{g⁺})/n`. -/
def gcdHarmonicSum (P : Finset ℕ) (d : ℕ → ℝ) (g : P → ℤ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), d n * (gcdPart P n (fun p => (g p).toNat) : ℝ) / n

/-- **The fibre sums of a twist polynomial.** -/
theorem sum_twistFibre_eq (hP : ∀ p ∈ P, p.Prime) (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ)
    {d : ℕ → ℝ} (hd0 : d 0 = 0) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1), d n * (Real.sqrt n)⁻¹ * twistMainWeight P A c n =
      ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
        gcdHarmonicSum P d (a - a') k := by
  unfold gcdHarmonicSum
  have e : ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
      ∑ n ∈ Finset.range (k + 1), d n * (gcdPart P n (fun p => ((a - a') p).toNat) : ℝ) / n =
      ∑ n ∈ Finset.range (k + 1), ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
        (d n * (gcdPart P n (fun p => ((a - a') p).toNat) : ℝ) / n) := by
    simp only [Finset.mul_sum]
    calc _ = ∑ a ∈ A, ∑ n ∈ Finset.range (k + 1), ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
          (d n * (gcdPart P n (fun p => ((a - a') p).toNat) : ℝ) / n) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hd0]
  rw [twistMainWeight_eq_gcd hP A c hn.ne']
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn0.le]
  have e2 : ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
      (d n * (gcdPart P n (fun p => ((a - a') p).toNat) : ℝ) / n) =
      d n / n * ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
        (gcdPart P n (fun p => ((a - a') p).toNat) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a' _ => by ring
  rw [e2, div_eq_mul_inv, ← hsq]
  ring

/-- **The notch Bochner law.** If `lam` is full-cone Weil-positive with notch-small deviation `d`,
and all gcd-harmonic sums `Γ(g) = Σ_n d(n) gcd(n, P^{g⁺})/n` converge, then for every finite `A ⊂ ℤ^P`
and coefficients `c`, `Σ_{a,a'} c_a c_{a'} (P^{|a−a'|})^{−1/2} Γ(a − a') ≤ 0`. -/
theorem notchBochner_le {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam)) (hP : ∀ p ∈ P, p.Prime)
    (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) {Γ : (P → ℤ) → ℝ}
    (hΓ : ∀ g, Tendsto (gcdHarmonicSum P (WeilOneSided.coneDeviation lam) g) atTop
      (𝓝 (Γ g))) :
    ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') * Γ (a - a') ≤ 0 := by
  by_contra hX
  push Not at hX
  have hd0 : WeilOneSided.coneDeviation lam 0 = 0 := by simp [WeilOneSided.coneDeviation]
  have hlim : Tendsto (fun k => ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') *
      gcdHarmonicSum P (WeilOneSided.coneDeviation lam) (a - a') k) atTop
      (𝓝 (∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') * Γ (a - a'))) :=
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun a' _ => (hΓ (a - a')).const_mul _
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (Ioi_mem_nhds (half_lt_self hX)))
  have hβ : ∀ a ∈ A, ∀ p, |a p| ≤ (fun p => A.sup fun a : P → ℤ => (a p).natAbs) p := by
    intro a ha p
    have := Finset.le_sup (f := fun a : P → ℤ => (a p).natAbs) ha
    rw [Int.abs_eq_natAbs]
    exact_mod_cast this
  have h := twistFibreSum_nonpos_of_weilPositiveFull hW hd hP A c hβ
    (Y := (∑ a ∈ A, ∑ a' ∈ A, c a * c a' * twistGramWeight (a - a') * Γ (a - a')) / 2) (T := T)
    fun k hk => by
      rw [sum_twistFibre_eq hP A c hd0 k]
      exact (hT k hk).le
  linarith

end RHTower.WeilAbscissa
