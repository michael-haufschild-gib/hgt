import GaloisForLFunctions.RHTower.WeilKloostermanDegreeSums

/-!
# The L-function of a Kloosterman sum (Hasse–Davenport form)

For any weight `w` on monic polynomials over a finite field that is multiplicative on monic
polynomials, the degree sums `s_m = Σ_{deg f = m} w f` and the prime-power sums
`c_j = Σ_{d | j} Σ_{P monic irreducible, deg P = d} d · w(P)^{j/d}` satisfy the Newton identity
`m · s_m = Σ_{j=1}^m c_j s_{m-j}` (`newton_identity`). It is proved from the degree formula
`deg f = Σ_{P^k | f} deg P` (unique factorization) and the bijection `f = P^k h`.

For the Kloosterman weight the degree sums are `1, K(a), q, 0, 0, …`, so
`c_1 = K`, `c_2 = 2q - K²`, `c_n = -K c_{n-1} - q c_{n-2}`, and there are `α, β` with `α + β = -K`,
`αβ = q`, `c_n = -(αⁿ + βⁿ)` (`klPower_closed_form`). This is step 2 of the elementary proof of
Weil's bound (card `weil-bound-kloosterman-lean`).
-/

open Polynomial Finset


namespace GaloisForLFunctions.RHTower.WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Degree sums of an arbitrary weight on monic polynomials. -/
noncomputable def degSumW (w : F[X] → ℂ) (m : ℕ) : ℂ := ∑ f ∈ monicDeg m, w f

/-- (S3) Summing a multiplicative weight over the multiples of `P^k` of degree `m`. -/
theorem sum_dvd_monicDeg (w : F[X] → ℂ)
    (hw : ∀ f g : F[X], f.Monic → g.Monic → w (f * g) = w f * w g)
    {P : F[X]} (hP : P.Monic) (k m : ℕ) :
    (∑ f ∈ (monicDeg m).filter (fun f => P ^ k ∣ f), w f) =
      if k * P.natDegree ≤ m then w (P ^ k) * degSumW w (m - k * P.natDegree) else 0 := by
  have hPk : (P ^ k).Monic := hP.pow k
  have hdeg : (P ^ k).natDegree = k * P.natDegree := by rw [hP.natDegree_pow]
  split_ifs with hle
  · rw [degSumW, Finset.mul_sum]
    symm
    apply Finset.sum_nbij' (fun h => P ^ k * h) (fun f => f /ₘ (P ^ k))
    · intro h hh
      rw [mem_monicDeg] at hh
      rw [Finset.mem_filter, mem_monicDeg]
      refine ⟨⟨hPk.mul hh.1, ?_⟩, dvd_mul_right _ _⟩
      rw [hPk.natDegree_mul hh.1, hdeg, hh.2]
      omega
    · intro f hf
      rw [Finset.mem_filter, mem_monicDeg] at hf
      rw [mem_monicDeg]
      obtain ⟨⟨hfm, hfd⟩, g, rfl⟩ := hf
      rw [mul_divByMonic_cancel_left g hPk]
      have hg : g.Monic := hPk.of_mul_monic_left hfm
      refine ⟨hg, ?_⟩
      rw [hPk.natDegree_mul hg, hdeg] at hfd
      omega
    · intro h _
      exact mul_divByMonic_cancel_left h hPk
    · intro f hf
      rw [Finset.mem_filter] at hf
      obtain ⟨-, g, rfl⟩ := hf
      rw [mul_divByMonic_cancel_left g hPk]
    · intro h hh
      rw [mem_monicDeg] at hh
      exact (hw _ _ hPk hh.1).symm
  · apply Finset.sum_eq_zero
    intro f hf
    rw [Finset.mem_filter, mem_monicDeg] at hf
    obtain ⟨⟨hfm, hfd⟩, g, rfl⟩ := hf
    exfalso
    have hg : g.Monic := hPk.of_mul_monic_left hfm
    rw [hPk.natDegree_mul hg, hdeg] at hfd
    omega

open UniqueFactorizationMonoid

omit [Fintype F] in
theorem monic_of_mem_nf {f P : F[X]} (hP : P ∈ normalizedFactors f) : P.Monic := by
  have h0 : P ≠ 0 := ne_zero_of_mem_normalizedFactors hP
  have hn := normalize_normalized_factor P hP
  rw [← hn]
  exact Polynomial.monic_normalize h0

omit [Fintype F] in
theorem pow_dvd_iff_le_count {P f : F[X]} (hP : Irreducible P) (hPm : P.Monic) (hf : f ≠ 0)
    (k : ℕ) : P ^ k ∣ f ↔ k ≤ (normalizedFactors f).count P := by
  rw [pow_dvd_iff_le_emultiplicity, le_emultiplicity_iff_replicate_le_normalizedFactors hP hf,
    hPm.normalize_eq_self, ← Multiset.le_count_iff_replicate_le]

omit [Fintype F] in
theorem prod_nf_eq {f : F[X]} (hf : f.Monic) : (normalizedFactors f).prod = f := by
  apply eq_of_monic_of_associated _ hf (prod_normalizedFactors hf.ne_zero)
  have := monic_multiset_prod_of_monic (normalizedFactors f) id
    (fun P hP => monic_of_mem_nf hP)
  simpa using this

omit [Fintype F] in
theorem natDegree_eq_sum_count {f : F[X]} (hf : f.Monic) :
    f.natDegree = ∑ P ∈ (normalizedFactors f).toFinset,
      (normalizedFactors f).count P * P.natDegree := by
  conv_lhs => rw [← prod_nf_eq hf]
  rw [natDegree_multiset_prod_of_monic _ (fun P hP => monic_of_mem_nf hP),
    Finset.sum_multiset_map_count]
  simp [smul_eq_mul]

omit [Fintype F] in
theorem count_le_natDegree {f P : F[X]} (hf : f.Monic) (hP : P ∈ normalizedFactors f) :
    (normalizedFactors f).count P ≤ f.natDegree := by
  have hd : 1 ≤ P.natDegree := by
    have hi := irreducible_of_normalized_factor P hP
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hi)
  rw [natDegree_eq_sum_count hf]
  calc (normalizedFactors f).count P ≤ (normalizedFactors f).count P * P.natDegree :=
        Nat.le_mul_of_pos_right _ hd
    _ ≤ _ := Finset.single_le_sum (f := fun Q => (normalizedFactors f).count Q * Q.natDegree)
        (fun _ _ => Nat.zero_le _) (Multiset.mem_toFinset.mpr hP)

/-- Monic irreducible polynomials of degree `d`. -/
noncomputable def irrDeg (d : ℕ) : Finset F[X] := (monicDeg d).filter Irreducible

theorem mem_irrDeg {d : ℕ} {P : F[X]} :
    P ∈ irrDeg d ↔ P.Monic ∧ P.natDegree = d ∧ Irreducible P := by
  rw [irrDeg, Finset.mem_filter, mem_monicDeg, and_assoc]

omit [Fintype F] in
theorem sum_k_indicator {P f : F[X]} (hP : Irreducible P) (hPm : P.Monic) (hf : f.Monic) {N : ℕ}
    (hN : f.natDegree ≤ N) (c : ℂ) :
    (∑ k ∈ Finset.Icc 1 N, if P ^ k ∣ f then c else 0) =
      ((normalizedFactors f).count P : ℂ) * c := by
  have hcN : (normalizedFactors f).count P ≤ N := by
    by_cases hmem : P ∈ normalizedFactors f
    · exact (count_le_natDegree hf hmem).trans hN
    · rw [Multiset.count_eq_zero.mpr hmem]; exact Nat.zero_le _
  have hiff : ∀ k, P ^ k ∣ f ↔ k ≤ (normalizedFactors f).count P :=
    pow_dvd_iff_le_count hP hPm hf.ne_zero
  simp_rw [hiff]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Finset.Icc 1 N).filter (fun k => k ≤ (normalizedFactors f).count P) =
      Finset.Icc 1 ((normalizedFactors f).count P) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]
  simp

/-- (S1) The degree of a monic polynomial as a sum over monic irreducible prime powers. -/
theorem natDegree_eq_sum_irr {f : F[X]} (hf : f.Monic) {N : ℕ} (hN : f.natDegree ≤ N) :
    (f.natDegree : ℂ) = ∑ d ∈ Finset.Icc 1 N, ∑ P ∈ irrDeg d,
      ∑ k ∈ Finset.Icc 1 N, if P ^ k ∣ f then (d : ℂ) else 0 := by
  have h1 : ∀ d ∈ Finset.Icc 1 N, ∀ P ∈ irrDeg (F := F) d,
      (∑ k ∈ Finset.Icc 1 N, if P ^ k ∣ f then (d : ℂ) else 0) =
        ((normalizedFactors f).count P : ℂ) * (P.natDegree : ℂ) := by
    intro d _ P hP
    rw [mem_irrDeg] at hP
    rw [sum_k_indicator hP.2.2 hP.1 hf hN, hP.2.1]
  rw [Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (h1 d hd))]
  rw [← Finset.sum_biUnion]
  · have hsub : (normalizedFactors f).toFinset ⊆ (Finset.Icc 1 N).biUnion (irrDeg (F := F)) := by
      intro P hP
      rw [Multiset.mem_toFinset] at hP
      rw [Finset.mem_biUnion]
      have hi := irreducible_of_normalized_factor P hP
      refine ⟨P.natDegree, ?_, mem_irrDeg.mpr ⟨monic_of_mem_nf hP, rfl, hi⟩⟩
      rw [Finset.mem_Icc]
      constructor
      · exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hi)
      · refine le_trans ?_ hN
        exact Polynomial.natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hP) hf.ne_zero
    rw [← Finset.sum_subset hsub]
    · rw [natDegree_eq_sum_count hf]
      push_cast
      rfl
    · intro P _ hP
      rw [Multiset.mem_toFinset] at hP
      rw [Multiset.count_eq_zero.mpr hP]
      simp
  · intro d _ e _ hde
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro P hPd hPe
    rw [mem_irrDeg] at hPd hPe
    exact hde (hPd.2.1.symm.trans hPe.2.1)

/-- Power sums `c_j = Σ_{d | j} Σ_{P monic irreducible, deg P = d} d · w(P)^{j/d}`. -/
noncomputable def powerSumW (w : F[X] → ℂ) (j : ℕ) : ℂ :=
  ∑ d ∈ j.divisors, ∑ P ∈ irrDeg d, (d : ℂ) * w P ^ (j / d)

/-- Reindexing pairs `(d, k)` with `dk ≤ m` by `(j, d)` with `d ∣ j ≤ m`. -/
theorem sum_pairs_eq_sum_divisors (m : ℕ) (g : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 m, if k * d ≤ m then g d k else 0) =
      ∑ j ∈ Finset.Icc 1 m, ∑ d ∈ j.divisors, g d (j / d) := by
  rw [← Finset.sum_product', Finset.sum_sigma', ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => ⟨y.2 * y.1, y.1⟩) (fun x => (x.2, x.1 / x.2))
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
    refine ⟨⟨?_, hy.2⟩, dvd_mul_left _ _, ?_⟩
    · nlinarith [hy.1.1.1, hy.1.2.1]
    · have := hy.1.1.1; have := hy.1.2.1; positivity
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    obtain ⟨⟨hj1, hjm⟩, ⟨e, he⟩, -⟩ := hx
    have hd : 0 < x.2 := Nat.pos_of_ne_zero (by rintro h0; rw [h0, zero_mul] at he; omega)
    have he' : x.1 / x.2 = e := by rw [he, Nat.mul_div_cancel_left _ hd]
    rw [he']
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro h0; rw [h0, mul_zero] at he; omega)
    refine ⟨⟨⟨hd, ?_⟩, he0, ?_⟩, ?_⟩
    · rw [he] at hjm; nlinarith
    · rw [he] at hjm; nlinarith
    · rw [he] at hjm; linarith [mul_comm x.2 e]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hy
    have h0 : 0 < y.1 := by omega
    ext
    · rfl
    · exact Nat.mul_div_cancel _ h0
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    obtain ⟨-, hdv, -⟩ := hx
    exact Sigma.ext (Nat.div_mul_cancel hdv) (by simp)
  · intro y _
    simp only
    congr 2
    have : 0 < y.1 := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at *
      omega
    rw [Nat.mul_div_cancel _ this]

/-- **Newton identity** for a multiplicative weight on monic polynomials:
`m · s_m = Σ_{j=1}^m c_j · s_{m-j}`. -/
theorem newton_identity (w : F[X] → ℂ)
    (hw : ∀ f g : F[X], f.Monic → g.Monic → w (f * g) = w f * w g) (hw1 : w 1 = 1) (m : ℕ) :
    (m : ℂ) * degSumW w m =
      ∑ j ∈ Finset.Icc 1 m, powerSumW w j * degSumW w (m - j) := by
  have hpow : ∀ P : F[X], P.Monic → ∀ k : ℕ, w (P ^ k) = w P ^ k := by
    intro P hP k
    induction k with
    | zero => simp [hw1]
    | succ k ih => rw [pow_succ, hw _ _ (hP.pow k) hP, ih, pow_succ]
  -- expand m via S1
  have hL : (m : ℂ) * degSumW w m = ∑ f ∈ monicDeg m, ∑ d ∈ Finset.Icc 1 m, ∑ P ∈ irrDeg d,
      ∑ k ∈ Finset.Icc 1 m, if P ^ k ∣ f then (d : ℂ) * w f else 0 := by
    rw [degSumW, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    rw [mem_monicDeg] at hf
    have h := natDegree_eq_sum_irr hf.1 (le_of_eq hf.2)
    rw [hf.2] at h
    rw [h, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp
  rw [hL, Finset.sum_comm]
  have hS3 : ∀ d ∈ Finset.Icc 1 m, ∀ P ∈ irrDeg (F := F) d, ∀ k : ℕ,
      (∑ f ∈ monicDeg m, if P ^ k ∣ f then (d : ℂ) * w f else 0) =
        if k * d ≤ m then (d : ℂ) * (w P ^ k * degSumW w (m - k * d)) else 0 := by
    intro d _ P hP k
    rw [mem_irrDeg] at hP
    have h := sum_dvd_monicDeg w hw hP.1 k m
    rw [hP.2.1, hpow P hP.1 k] at h
    rw [← Finset.sum_filter, ← Finset.mul_sum, h]
    split_ifs <;> simp
  have hstep : (∑ d ∈ Finset.Icc 1 m, ∑ f ∈ monicDeg m, ∑ P ∈ irrDeg d,
      ∑ k ∈ Finset.Icc 1 m, if P ^ k ∣ f then (d : ℂ) * w f else 0) =
      ∑ d ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 m, if k * d ≤ m then
        (∑ P ∈ irrDeg (F := F) d, (d : ℂ) * w P ^ k) * degSumW w (m - k * d) else 0 := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun P _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_congr rfl (fun P hP => hS3 d hd P hP k)]
    split_ifs
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      ring
    · simp
  rw [hstep, sum_pairs_eq_sum_divisors m
    (fun d k => (∑ P ∈ irrDeg (F := F) d, (d : ℂ) * w P ^ k) * degSumW w (m - k * d))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [powerSumW, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]

section kloosterman
variable (ψ : AddChar F ℂ) (a : F)

omit [Fintype F] in
theorem klW_one : klW ψ a (1 : F[X]) = 1 := by
  simp [klW, Polynomial.nextCoeff, Polynomial.coeff_one]

/-- Power sums of the Kloosterman weight: `c_n = Σ_{d|n} Σ_{P} d·λ(P)^{n/d}`. -/
noncomputable def klPower (n : ℕ) : ℂ := powerSumW (klW ψ a) n

omit [Fintype F] in
theorem klW_mul' : ∀ f g : F[X], f.Monic → g.Monic → klW ψ a (f * g) = klW ψ a f * klW ψ a g :=
  fun _ _ hf hg => klW_mul ψ a hf hg

theorem degSumW_klW (m : ℕ) : degSumW (klW ψ a) m = degSum ψ a m := rfl

theorem klPower_one : klPower ψ a 1 = kloosterman ψ a := by
  have h := newton_identity (klW ψ a) (klW_mul' ψ a) (klW_one ψ a) 1
  simp only [degSumW_klW, degSum_one, Nat.cast_one, one_mul, Finset.Icc_self,
    Finset.sum_singleton, Nat.sub_self, degSum_zero, mul_one] at h
  exact h.symm

theorem klPower_two (hψ : ψ.IsPrimitive) (ha : a ≠ 0) :
    klPower ψ a 2 = 2 * Fintype.card F - kloosterman ψ a ^ 2 := by
  have h := newton_identity (klW ψ a) (klW_mul' ψ a) (klW_one ψ a) 2
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  simp only [degSumW_klW, hI] at h
  have h1 := klPower_one ψ a
  unfold klPower at h1 ⊢
  rw [Finset.sum_pair (by norm_num), degSum_two ψ a hψ ha, degSum_one, degSum_zero, h1] at h
  norm_num at h
  linear_combination -h

theorem klPower_rec (hψ : ψ.IsPrimitive) (ha : a ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    klPower ψ a n = -kloosterman ψ a * klPower ψ a (n - 1) -
      Fintype.card F * klPower ψ a (n - 2) := by
  have hne : ψ ≠ 1 := by
    have := hψ one_ne_zero
    rwa [AddChar.mulShift_one] at this
  have h := newton_identity (klW ψ a) (klW_mul' ψ a) (klW_one ψ a) n
  simp only [degSumW_klW] at h
  rw [degSum_ge_three ψ a hne hn, mul_zero] at h
  have hsplit : Finset.Icc 1 n = (Finset.Icc 1 (n - 3)) ∪ {n - 2, n - 1, n} := by
    ext j; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton]; omega
  rw [hsplit, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro j hj hj'
    simp only [Finset.mem_Icc] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    omega)] at h
  have hzero : (∑ j ∈ Finset.Icc 1 (n - 3), powerSumW (klW ψ a) j * degSum ψ a (n - j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [degSum_ge_three ψ a hne (by omega), mul_zero]
  have hd1 : n - 2 ≠ n - 1 := by omega
  have hd2 : n - 2 ≠ n := by omega
  have hd3 : n - 1 ≠ n := by omega
  rw [Finset.sum_insert (by simp [hd1, hd2]), Finset.sum_insert (by simp [hd3]),
    Finset.sum_singleton] at h
  have e1 : n - (n - 2) = 2 := by omega
  have e2 : n - (n - 1) = 1 := by omega
  rw [hzero, e1, e2, Nat.sub_self, degSum_two ψ a hψ ha, degSum_one, degSum_zero] at h
  unfold klPower
  linear_combination -h

/-- **Hasse–Davenport form of the Kloosterman power sums.** There are `α, β ∈ ℂ` with
`α + β = -K(a)`, `αβ = q`, and `c_n = -(αⁿ + βⁿ)` for every `n ≥ 1`. -/
theorem klPower_closed_form (hψ : ψ.IsPrimitive) (ha : a ≠ 0) :
    ∃ α β : ℂ, α + β = -kloosterman ψ a ∧ α * β = (Fintype.card F : ℂ) ∧
      ∀ n, 1 ≤ n → klPower ψ a n = -(α ^ n + β ^ n) := by
  set K := kloosterman ψ a
  set q : ℂ := (Fintype.card F : ℂ)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (K ^ 2 - 4 * q) (by norm_num : 0 < 2)
  refine ⟨(-K + s) / 2, (-K - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs, ?_⟩
  set α := (-K + s) / 2
  set β := (-K - s) / 2
  have hsum : α + β = -K := by ring
  have hprod : α * β = q := by simp only [α, β]; linear_combination (-1 / 4 : ℂ) * hs
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h1 | h2 | h3
    · subst h1; rw [klPower_one]; simp only [pow_one]; rw [hsum]; ring
    · subst h2; rw [klPower_two ψ a hψ ha]
      have : α ^ 2 + β ^ 2 = (α + β) ^ 2 - 2 * (α * β) := by ring
      rw [this, hsum, hprod]; ring
    · rw [klPower_rec ψ a hψ ha h3, ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega)]
      have e1 : α ^ n = α ^ (n - 1) * α := by rw [← pow_succ]; congr 1; omega
      have e2 : β ^ n = β ^ (n - 1) * β := by rw [← pow_succ]; congr 1; omega
      have e3 : α ^ (n - 1) = α ^ (n - 2) * α := by rw [← pow_succ]; congr 1; omega
      have e4 : β ^ (n - 1) = β ^ (n - 2) * β := by rw [← pow_succ]; congr 1; omega
      rw [e1, e2, e3, e4]
      change -K * _ - q * _ = _
      rw [← hsum, ← hprod]
      ring

end kloosterman

end GaloisForLFunctions.RHTower.WeilKloosterman
