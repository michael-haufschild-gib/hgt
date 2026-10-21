import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumMajorant

/-!
# Heath-Brown's pair sums: comparison of lengths by dilation

Heath-Brown's Lemma 2 says, morally, that the weighted pair sum

`𝒜_σ(S) = Σ_{t₁,t₂∈W} |Σ_{n∈S} n^{−σ+i(t₁−t₂)}|² = Σ_{n,m∈S} n^{−σ} m^{−σ} K(n,m)`

does not decrease when the support moves to longer integers.  Literal monotonicity in the dyadic
length is false (ratios `n/m` close to `2` with `n, m ≍ M` need not occur among integers of a
longer dyadic block), so this file proves a precise substitute by dilation.

The kernel `K(n,m) = |Σ_{t∈W} n^{it} m^{−it}|²` depends only on the ratio `n/m`:
`K(jn, jm) = K(n,m)`.  Hence every dilation `(n, m) ↦ (jn, jm)` with `j ∈ J` carries the terms of
`𝒜_σ(S)` to terms of `𝒜_σ(L)` with weight `j^{−2σ}`, provided `jS ⊆ L`.  A pair `(u, v) ∈ L²` is hit
by at most `d(u)` triples `(j, n, m)`, since `j | u` determines `n = u/j` and `m = v/j`.  Summing,

`(Σ_{j∈J} j^{−2σ}) · 𝒜_σ(S) ≤ max_{u∈L} d(u) · 𝒜_σ(L)`.

With `J = (q, 2q]`, `q = ⌊N/A⌋`, a block `S ⊆ (A, cA]` is carried into `(N, 2cN]` for every
`N ≥ A`; for `σ = 1/2` the weight is `Σ_J 1/j ≥ 1/2`, so `𝒜_{1/2}(S) ≤ 2D 𝒜_{1/2}((N, 2cN])`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset ComplexConjugate

noncomputable section

/-- Heath-Brown's weighted pair sum `𝒜_σ(S) = Σ_{t₁,t₂∈W}|Σ_{n∈S} n^{−σ+i(t₁−t₂)}|²`. -/
def hbAmp (W : Finset ℝ) (σ : ℝ) (S : Finset ℕ) : ℝ :=
  hbPairSum W S (fun n => (((n : ℝ) ^ (-σ) : ℝ) : ℂ))

theorem hbAmp_nonneg (W : Finset ℝ) (σ : ℝ) (S : Finset ℕ) :
    0 ≤ hbAmp W σ S :=
  hbPairSum_nonneg W S _

/-- **The kernel depends only on the ratio:** `K(jn, jm) = K(n, m)`. -/
theorem hbKernel_mul_mul (W : Finset ℝ) {j n m : ℕ} (hj : j ≠ 0)
    (hn : n ≠ 0) (hm : m ≠ 0) : hbKernel W (j * n) (j * m) = hbKernel W n m := by
  have hterm : ∀ t, hbPhase (j * n) t * conj (hbPhase (j * m) t) =
      hbPhase n t * conj (hbPhase m t) := fun t => by
    rw [hbPhase_mul hj hn, hbPhase_mul hj hm, map_mul]
    calc hbPhase j t * hbPhase n t * (conj (hbPhase j t) * conj (hbPhase m t))
        = (hbPhase j t * conj (hbPhase j t)) * (hbPhase n t * conj (hbPhase m t)) := by ring
      _ = hbPhase n t * conj (hbPhase m t) := by rw [hbPhase_mul_conj_self, one_mul]
  simp only [hbKernel, hterm]

/-- **Heath-Brown's Lemma 2, dilation form.**  If `jS ⊆ L` for every `j ∈ J` (all of `S`, `J`
positive) and `d(u) ≤ D` on `L`, then `(Σ_{j∈J} j^{−2σ}) 𝒜_σ(S) ≤ D · 𝒜_σ(L)`. -/
theorem sum_rpow_sq_mul_hbAmp_le (W : Finset ℝ) (σ : ℝ)
    {S L J : Finset ℕ} (hS : (0 : ℕ) ∉ S) (hJ : (0 : ℕ) ∉ J)
    (hmap : ∀ j ∈ J, ∀ n ∈ S, j * n ∈ L) {D : ℝ}
    (hD : ∀ u ∈ L, (u.divisors.card : ℝ) ≤ D) :
    (∑ j ∈ J, ((j : ℝ) ^ (-σ)) ^ 2) * hbAmp W σ S ≤ D * hbAmp W σ L := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun n : ℕ => (n : ℝ) ^ (-σ) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → ℝ, F = fun u v => w u * w v * hbKernel W u v := ⟨_, rfl⟩
  have hw0 : ∀ n, 0 ≤ w n := fun n => by rw [hw]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hF0 : ∀ u v, 0 ≤ F u v := fun u v => by
    rw [hF]; exact mul_nonneg (mul_nonneg (hw0 u) (hw0 v)) (hbKernel_nonneg W u v)
  have hAmp : ∀ T : Finset ℕ, hbAmp W σ T = ∑ u ∈ T, ∑ v ∈ T, F u v := fun T => by
    rw [hbAmp, hbPairSum_ofReal, hF, hw]
  -- each dilation carries a term of `𝒜_σ(S)` to a term of `𝒜_σ(L)` with weight `j^{−2σ}`
  have hscale : ∀ j ∈ J, ∀ n ∈ S, ∀ m ∈ S, w j ^ 2 * F n m = F (j * n) (j * m) := by
    intro j hj n hn m hm
    simp only [hF]
    rw [hbKernel_mul_mul W (ne_of_mem_of_not_mem hj hJ) (ne_of_mem_of_not_mem hn hS)
      (ne_of_mem_of_not_mem hm hS)]
    simp only [hw, Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hLHS : (∑ j ∈ J, w j ^ 2) * ∑ n ∈ S, ∑ m ∈ S, F n m =
      ∑ x ∈ J ×ˢ (S ×ˢ S), F (x.1 * x.2.1) (x.1 * x.2.2) := by
    rw [Finset.sum_mul, Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m hm => hscale j hj n hn m hm
  have hmaps : ∀ x ∈ J ×ˢ (S ×ˢ S), (x.1 * x.2.1, x.1 * x.2.2) ∈ L ×ˢ L := by
    intro x hx
    obtain ⟨hj, hn, hm⟩ : x.1 ∈ J ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S := by
      simpa only [Finset.mem_product] using hx
    exact Finset.mem_product.mpr ⟨hmap _ hj _ hn, hmap _ hj _ hm⟩
  -- a pair `(u,v)` is hit by at most `d(u)` triples
  have hfib : ∀ y ∈ L ×ˢ L,
      ∑ x ∈ (J ×ˢ (S ×ˢ S)).filter (fun x => (x.1 * x.2.1, x.1 * x.2.2) = y),
        F (x.1 * x.2.1) (x.1 * x.2.2) ≤ D * F y.1 y.2 := by
    intro y hy
    have heq : ∀ x ∈ (J ×ˢ (S ×ˢ S)).filter (fun x => (x.1 * x.2.1, x.1 * x.2.2) = y),
        F (x.1 * x.2.1) (x.1 * x.2.2) = F y.1 y.2 := fun x hx => by
      rw [← (Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hF0 _ _)
    have hcard : ((J ×ˢ (S ×ˢ S)).filter
        (fun x => (x.1 * x.2.1, x.1 * x.2.2) = y)).card ≤ y.1.divisors.card := by
      refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) ?_
      · obtain ⟨hxX, hxy⟩ := Finset.mem_filter.mp hx
        obtain ⟨hj, hn, -⟩ : x.1 ∈ J ∧ x.2.1 ∈ S ∧ x.2.2 ∈ S := by
          simpa only [Finset.mem_product] using hxX
        have hy1 : x.1 * x.2.1 = y.1 := congrArg Prod.fst hxy
        rw [Finset.mem_coe, Nat.mem_divisors]
        refine ⟨⟨x.2.1, hy1.symm⟩, ?_⟩
        rw [← hy1]
        exact Nat.mul_ne_zero (ne_of_mem_of_not_mem hj hJ) (ne_of_mem_of_not_mem hn hS)
      · intro x hx x' hx' hxx'
        obtain ⟨hxX, hxy⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxX', hxy'⟩ := Finset.mem_filter.mp hx'
        have hj : x.1 ≠ 0 := ne_of_mem_of_not_mem (Finset.mem_product.mp hxX).1 hJ
        have h1 : x.1 * x.2.1 = x'.1 * x'.2.1 :=
          (congrArg Prod.fst hxy).trans (congrArg Prod.fst hxy').symm
        have h2 : x.1 * x.2.2 = x'.1 * x'.2.2 :=
          (congrArg Prod.snd hxy).trans (congrArg Prod.snd hxy').symm
        simp only at hxx'
        rw [← hxx'] at h1 h2
        exact Prod.ext hxx' (Prod.ext (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj) h1)
          (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj) h2))
    exact (Nat.cast_le.mpr hcard).trans (hD y.1 (Finset.mem_product.mp hy).1)
  have hwj : ∑ j ∈ J, ((j : ℝ) ^ (-σ)) ^ 2 = ∑ j ∈ J, w j ^ 2 := by rw [hw]
  rw [hwj, hAmp S, hAmp L, hLHS, ← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ y ∈ L ×ˢ L, ∑ x ∈ (J ×ˢ (S ×ˢ S)).filter (fun x => (x.1 * x.2.1, x.1 * x.2.2) = y),
        F (x.1 * x.2.1) (x.1 * x.2.2)
      ≤ ∑ y ∈ L ×ˢ L, D * F y.1 y.2 := Finset.sum_le_sum hfib
    _ = D * ∑ u ∈ L, ∑ v ∈ L, F u v := by rw [← Finset.mul_sum, Finset.sum_product]

/-- The dilation range `J = (q, 2q]` with `q = ⌊N/A⌋` carries `(A, cA]` into `(N, 2cN]`. -/
private theorem mul_mem_Ioc_of_dilate {A N c j n : ℕ} (hA : 0 < A)
    (hj : j ∈ Finset.Ioc (N / A) (2 * (N / A))) (hn : n ∈ Finset.Ioc A (c * A)) :
    j * n ∈ Finset.Ioc N (2 * c * N) := by
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.mp hj
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
  have hlt : N < A * (N / A + 1) := Nat.lt_mul_div_succ N hA
  have hqA : N / A * A ≤ N := Nat.div_mul_le_self N A
  refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
  · calc N < A * (N / A + 1) := hlt
      _ ≤ n * j := Nat.mul_le_mul hn1.le hj1
      _ = j * n := Nat.mul_comm n j
  · calc j * n ≤ (2 * (N / A)) * (c * A) := Nat.mul_le_mul hj2 hn2
      _ = 2 * c * (N / A * A) := by ring
      _ ≤ 2 * c * N := Nat.mul_le_mul_left _ hqA

/-- `Σ_{q<j≤2q} 1/j ≥ 1/2`. -/
private theorem half_le_sum_inv_Ioc {q : ℕ} (hq : 0 < q) :
    (1 / 2 : ℝ) ≤ ∑ j ∈ Finset.Ioc q (2 * q), ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
  have hterm : ∀ j ∈ Finset.Ioc q (2 * q), 1 / (2 * (q : ℝ)) ≤ ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.mp hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hpow : ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (j : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hjpos.le, ← Real.rpow_neg_one]
      norm_num
    rw [hpow, one_div]
    exact inv_anti₀ hjpos (show (j : ℝ) ≤ 2 * q by exact_mod_cast hj2)
  have hcard : ((Finset.Ioc q (2 * q)).card : ℝ) = q := by
    rw [Nat.card_Ioc]
    push_cast [show 2 * q - q = q by omega]
    ring
  calc (1 / 2 : ℝ) = (q : ℝ) * (1 / (2 * q)) := by field_simp
    _ = ((Finset.Ioc q (2 * q)).card : ℝ) * (1 / (2 * q)) := by rw [hcard]
    _ = ∑ _j ∈ Finset.Ioc q (2 * q), 1 / (2 * (q : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- **Heath-Brown's Lemma 2, block form.**  For `1 ≤ A ≤ N`, `S ⊆ (A, cA]` and `d(u) ≤ D` on
`(N, 2cN]`: `𝒜_{1/2}(S) ≤ 2D · 𝒜_{1/2}((N, 2cN])`. -/
theorem hbAmp_half_le_of_le (W : Finset ℝ) {A N c : ℕ} (hA : 0 < A)
    (hAN : A ≤ N) {S : Finset ℕ} (hS : S ⊆ Finset.Ioc A (c * A)) {D : ℝ}
    (hD : ∀ u ∈ Finset.Ioc N (2 * c * N), (u.divisors.card : ℝ) ≤ D) :
    hbAmp W (1 / 2) S ≤ 2 * D * hbAmp W (1 / 2) (Finset.Ioc N (2 * c * N)) := by
  have hq : 0 < N / A := Nat.div_pos hAN hA
  have hS0 : (0 : ℕ) ∉ S := fun h0 => by
    have := Finset.mem_Ioc.mp (hS h0); omega
  have hJ0 : (0 : ℕ) ∉ Finset.Ioc (N / A) (2 * (N / A)) := fun h0 => by
    have := Finset.mem_Ioc.mp h0; omega
  have hmain := sum_rpow_sq_mul_hbAmp_le W (1 / 2) hS0 hJ0
    (fun j hj n hn => mul_mem_Ioc_of_dilate hA hj (hS hn)) hD
  have hsum := half_le_sum_inv_Ioc hq
  have hA0 := hbAmp_nonneg W (1 / 2) S
  nlinarith [mul_le_mul_of_nonneg_right hsum hA0]

end

end RHTower.Sieve
