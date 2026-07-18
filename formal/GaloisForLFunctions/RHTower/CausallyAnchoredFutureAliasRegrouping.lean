import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

/-!
# Causally anchored future-alias regrouping

In a fixed causal anchor `c`, the unrestricted frequency sum attached to a squarefree future packet
`N` collapses onto frequencies coprime to the *future remainder* alone.  The anchor is never
reduced.

The mechanism is a bijection.  Writing `d = gcd (m, |k|)`, every pair `(m, k)` with `m ∣ N` and
`k ≠ 0` factors uniquely as `m = r * d`, `k = u * d` with `u` coprime to `r`, and conversely.  The
frequency `k / (c * m) = u / (c * r)` is invariant under this reduction, while the root sum picks up
exactly the root count of the removed part.  Summing the `d` fibre produces the local survival Euler
product.

`causalPairSet` together with `causalPair_image` is the reusable core; the regrouping identity is
`causallyAnchoredFutureAliasRegrouping`.
-/

open scoped BigOperators

namespace RHTower

/-! ## A finite disjoint family regrouping for finitely supported sums

`finsum_mem_iUnion` requires each piece of the family to be finite.  The pieces below are infinite
frequency fibres, so the regrouping is redone requiring only that each piece meets the support
finitely. -/

theorem finsum_mem_finset_biUnion_of_support_finite {α ι M : Type*} [AddCommMonoid M]
    {f : α → M} {t : ι → Set α} (D : Finset ι)
    (hdisj : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → Disjoint (t i) (t j))
    (hfin : ∀ i ∈ D, (t i ∩ Function.support f).Finite) :
    ∑ᶠ (x : α) (_ : x ∈ ⋃ i ∈ (D : Set ι), t i), f x =
      ∑ i ∈ D, ∑ᶠ (x : α) (_ : x ∈ t i), f x := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert i D hi ih =>
      have hdisj' : ∀ a ∈ D, ∀ b ∈ D, a ≠ b → Disjoint (t a) (t b) := fun a ha b hb hab =>
        hdisj a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
      have hfin' : ∀ a ∈ D, (t a ∩ Function.support f).Finite := fun a ha =>
        hfin a (Finset.mem_insert_of_mem ha)
      have hunion : ⋃ j ∈ ((insert i D : Finset ι) : Set ι), t j =
          t i ∪ ⋃ j ∈ (D : Set ι), t j := by
        simp [Finset.coe_insert]
      have hdisj_union : Disjoint (t i) (⋃ j ∈ (D : Set ι), t j) := by
        rw [Set.disjoint_iUnion₂_right]
        intro j hj
        exact hdisj i (Finset.mem_insert_self i D) j (Finset.mem_insert_of_mem hj)
          (fun hij => hi (hij ▸ hj))
      have hfin_i : (t i ∩ Function.support f).Finite := hfin i (Finset.mem_insert_self i D)
      have hfin_rest : ((⋃ j ∈ (D : Set ι), t j) ∩ Function.support f).Finite := by
        rw [Set.iUnion₂_inter]
        exact Set.Finite.biUnion D.finite_toSet fun j hj => hfin' j hj
      rw [hunion, finsum_mem_union' hdisj_union hfin_i hfin_rest,
        Finset.sum_insert hi, ih hdisj' hfin']

/-- Pulling a constant through a finitely supported conditional sum. -/
theorem mul_finsum_cond {α : Type*} (C : ℂ) (P : α → Prop) (f : α → ℂ) :
    C * (∑ᶠ (a : α) (_ : P a), f a) = ∑ᶠ (a : α) (_ : P a), C * f a := by
  classical
  have key : ∀ g : α → ℂ,
      (∑ᶠ (a : α) (_ : P a), g a) = ∑ᶠ (a : α), Set.indicator {x | P x} g a :=
    fun g => finsum_mem_def {x | P x} g
  rw [key f, key (fun a => C * f a), mul_finsum]
  refine finsum_congr fun a => ?_
  by_cases ha : P a <;> simp [ha]

/-! ## The causal pair set -/

/-- Pairs `(d, u)` of a complementary divisor `d ∣ m` and a nonzero frequency `u` coprime to the
future remainder `m / d`.  These index the reduced form of an arbitrary nonzero frequency. -/
def causalPairSet (m : ℕ) : Set (ℕ × ℤ) :=
  {p | p.1 ∣ m ∧ p.2 ≠ 0 ∧ (p.2.natAbs).Coprime (m / p.1)}

/-- The fibre of `causalPairSet` above a fixed complementary divisor. -/
def causalFibre (m d : ℕ) : Set (ℕ × ℤ) :=
  {p | p.1 = d ∧ p.2 ≠ 0 ∧ (p.2.natAbs).Coprime (m / d)}

theorem causalPairSet_eq_biUnion {m : ℕ} (hm : m ≠ 0) :
    causalPairSet m = ⋃ d ∈ (m.divisors : Set ℕ), causalFibre m d := by
  ext p
  simp only [causalPairSet, causalFibre, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe,
    Nat.mem_divisors, exists_prop]
  constructor
  · rintro ⟨hd, hu, hcop⟩
    exact ⟨p.1, ⟨hd, hm⟩, rfl, hu, hcop⟩
  · rintro ⟨d, ⟨hd, -⟩, hp1, hu, hcop⟩
    exact ⟨hp1 ▸ hd, hu, hp1 ▸ hcop⟩

theorem causalFibre_disjoint {m : ℕ} {d e : ℕ} (hde : d ≠ e) :
    Disjoint (causalFibre m d) (causalFibre m e) := by
  rw [Set.disjoint_left]
  rintro p ⟨hp, -, -⟩ ⟨hq, -, -⟩
  exact hde (hp ▸ hq ▸ rfl)

/-- On the causal pair set the map `(d, u) ↦ u * d` remembers `d` as `gcd (m, |u * d|)`: the causal
reduction is already maximal on the complementary coordinates. -/
theorem causalPair_gcd {m : ℕ} {p : ℕ × ℤ} (hp : p ∈ causalPairSet m) :
    m.gcd (p.2 * p.1).natAbs = p.1 := by
  obtain ⟨hd, -, hcop⟩ := hp
  have hnat : (p.2 * (p.1 : ℤ)).natAbs = p.2.natAbs * p.1 := by
    simp [Int.natAbs_mul]
  have hm_eq : m = m / p.1 * p.1 := (Nat.div_mul_cancel hd).symm
  have hg : Nat.gcd (m / p.1) p.2.natAbs = 1 := hcop.symm
  calc m.gcd (p.2 * (p.1 : ℤ)).natAbs
      = (m / p.1 * p.1).gcd (p.2.natAbs * p.1) := by
        rw [hnat]; conv_lhs => rw [hm_eq]
    _ = Nat.gcd (m / p.1) p.2.natAbs * p.1 := Nat.gcd_mul_right _ _ _
    _ = p.1 := by rw [hg, one_mul]

theorem causalPair_injOn {m : ℕ} (hm : m ≠ 0) :
    Set.InjOn (fun p : ℕ × ℤ => p.2 * p.1) (causalPairSet m) := by
  intro p hp q hq hpq
  simp only at hpq
  have hfst : p.1 = q.1 := by
    rw [← causalPair_gcd hp, ← causalPair_gcd hq, hpq]
  have hd0 : p.1 ≠ 0 := by
    intro h0
    exact hm (Nat.eq_zero_of_zero_dvd (h0 ▸ hp.1))
  have hcast : (q.1 : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (hfst ▸ hd0)
  rw [hfst] at hpq
  exact Prod.ext hfst (mul_right_cancel₀ hcast hpq)

/-- **Causal reduction is a bijection onto the nonzero frequencies.**  Against a squarefree modulus
every nonzero frequency has exactly one causal factorization. -/
theorem causalPair_image {m : ℕ} (hm : Squarefree m) :
    (fun p : ℕ × ℤ => p.2 * p.1) '' (causalPairSet m) = {k : ℤ | k ≠ 0} := by
  ext k
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hd0 : p.1 ≠ 0 := fun h0 => hm.ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hp.1))
    exact mul_ne_zero hp.2.1 (Nat.cast_ne_zero.mpr hd0)
  · intro hk
    have hdk : ((m.gcd k.natAbs : ℕ) : ℤ) ∣ k := by
      rw [Int.natCast_dvd]
      exact Nat.gcd_dvd_right m k.natAbs
    have hcancel : k / ((m.gcd k.natAbs : ℕ) : ℤ) * ((m.gcd k.natAbs : ℕ) : ℤ) = k :=
      Int.ediv_mul_cancel hdk
    have hu0 : k / ((m.gcd k.natAbs : ℕ) : ℤ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcancel
      exact hk hcancel.symm
    exact ⟨(m.gcd k.natAbs, k / ((m.gcd k.natAbs : ℕ) : ℤ)),
      ⟨Nat.gcd_dvd_left _ _, hu0,
        (causalGCDReduction_complement_coprime hm.ne_zero k).symm⟩, hcancel⟩

/-- Reindexing an unrestricted nonzero-frequency sum by the causal pair set.  This is the bijection
alone; no finiteness is needed. -/
theorem finsum_nonzero_eq_finsum_causalPairSet {M : Type*} [AddCommMonoid M]
    {m : ℕ} (hm : Squarefree m) (g : ℤ → M) :
    ∑ᶠ (k : ℤ) (_ : k ≠ 0), g k =
      ∑ᶠ (p : ℕ × ℤ) (_ : p ∈ causalPairSet m), g (p.2 * p.1) := by
  have himg := finsum_mem_image (f := g) (causalPair_injOn hm.ne_zero)
  rw [causalPair_image hm] at himg
  exact himg

/-- Reindexing one causal fibre by its reduced frequency. -/
theorem finsum_causalFibre {M : Type*} [AddCommMonoid M] (m d : ℕ) (G : ℕ × ℤ → M) :
    ∑ᶠ (p : ℕ × ℤ) (_ : p ∈ causalFibre m d), G p =
      ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime (m / d)), G (d, u) := by
  have hinj : Set.InjOn (fun u : ℤ => ((d, u) : ℕ × ℤ))
      {u : ℤ | u ≠ 0 ∧ (u.natAbs).Coprime (m / d)} := by
    intro a _ b _ hab
    exact (Prod.mk.injEq _ _ _ _ ▸ hab : (d, a) = (d, b)) |> fun h => (Prod.ext_iff.mp h).2
  have hset : (fun u : ℤ => ((d, u) : ℕ × ℤ)) ''
      {u : ℤ | u ≠ 0 ∧ (u.natAbs).Coprime (m / d)} = causalFibre m d := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_setOf_eq, causalFibre, Prod.mk.injEq]
    constructor
    · rintro ⟨u, ⟨hu, hcop⟩, rfl, rfl⟩
      exact ⟨rfl, hu, hcop⟩
    · rintro ⟨rfl, hb, hcop⟩
      exact ⟨b, ⟨hb, hcop⟩, rfl, rfl⟩
  have himg := finsum_mem_image (f := G) hinj
  rw [hset] at himg
  exact himg

/-- **Causal fibre regrouping.**  An unrestricted nonzero-frequency sum with finite support splits
into the complementary divisor sum of its reduced-frequency sums. -/
theorem finsum_nonzero_eq_sum_divisors_finsum {M : Type*} [AddCommMonoid M]
    {m : ℕ} (hm : Squarefree m) (g : ℤ → M) (hg : (Function.support g).Finite) :
    ∑ᶠ (k : ℤ) (_ : k ≠ 0), g k =
      ∑ d ∈ m.divisors,
        ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime (m / d)), g (u * d) := by
  classical
  rw [finsum_nonzero_eq_finsum_causalPairSet hm g, causalPairSet_eq_biUnion hm.ne_zero]
  have hfin : ∀ d ∈ m.divisors,
      (causalFibre m d ∩ Function.support (fun p : ℕ × ℤ => g (p.2 * p.1))).Finite := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hinj : Set.InjOn (fun p : ℕ × ℤ => p.2 * p.1) (causalFibre m d) := by
      rintro p ⟨hp, -, -⟩ q ⟨hq, -, -⟩ hpq
      simp only [hp, hq] at hpq
      exact Prod.ext (hp.trans hq.symm) (mul_right_cancel₀ (Nat.cast_ne_zero.mpr hd0) hpq)
    refine Set.Finite.of_finite_image (hg.subset ?_) (hinj.mono Set.inter_subset_left)
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  rw [finsum_mem_finset_biUnion_of_support_finite m.divisors
    (fun i _ j _ hij => causalFibre_disjoint hij) hfin]
  exact Finset.sum_congr rfl fun d _ => finsum_causalFibre m d (fun p => g (p.2 * p.1))

/-! ## The divisor reindexing -/

/-- Divisor-pair reindexing `(m, d) ↦ (m / d, d)`: summing over a divisor of each divisor of `N` is
the same as summing over a divisor of each complementary quotient. -/
theorem sum_divisors_sum_divisors_reindex {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : N ≠ 0)
    (f : ℕ → ℕ → M) :
    ∑ m ∈ N.divisors, ∑ d ∈ m.divisors, f m d =
      ∑ r ∈ N.divisors, ∑ d ∈ (N / r).divisors, f (r * d) d := by
  classical
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [Finset.sum_sigma' N.divisors (fun m => m.divisors) (fun m d => f m d),
    Finset.sum_sigma' N.divisors (fun r => (N / r).divisors) (fun r d => f (r * d) d)]
  refine Finset.sum_nbij' (i := fun x => ⟨x.1 / x.2, x.2⟩) (j := fun x => ⟨x.1 * x.2, x.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hmN, -⟩, hdm, hm0⟩ := hx
    have hd0 : d ≠ 0 := fun h => hm0 (Nat.eq_zero_of_zero_dvd (h ▸ hdm))
    have hmd : m / d ∣ N := (Nat.div_dvd_of_dvd hdm).trans hmN
    have hmdpos : 0 < m / d :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdm) (Nat.pos_of_ne_zero hd0)
    refine ⟨⟨hmd, hN⟩, ?_, (Nat.div_pos (Nat.le_of_dvd hNpos hmd) hmdpos).ne'⟩
    rw [Nat.dvd_div_iff_mul_dvd hmd, Nat.div_mul_cancel hdm]
    exact hmN
  · rintro ⟨r, d⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hrN, -⟩, hdq, -⟩ := hx
    have hrd : r * d ∣ N := (Nat.dvd_div_iff_mul_dvd hrN).mp hdq
    exact ⟨⟨hrd, hN⟩, dvd_mul_left d r, fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hrd))⟩
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx
    simp only [Nat.div_mul_cancel hx.2.1]
  · rintro ⟨r, d⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact absurd (by simpa [h] using hx.2.1) hx.2.2
      · exact h
    simp only [Nat.mul_div_cancel _ hd0]
  · rintro ⟨m, d⟩ hx
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hx
    simp only [Nat.div_mul_cancel hx.2.1]

/-! ## The regrouping theorem -/

/-- **Causally anchored future-alias regrouping.**  For a causal anchor `c` coprime to a squarefree
future packet `N`, the unrestricted Möbius frequency sum equals a sum over future remainders `r`
whose frequencies are restricted to be coprime to `r` alone — the anchor `c` is never reduced —
each weighted by the local survival Euler product of the removed part. -/
theorem causallyAnchoredFutureAliasRegrouping
    {c N : ℕ} (hc : c ≠ 0) (hN : Squarefree N) (hcN : c.Coprime N)
    (h : ℤ) (F : ℚ → ℂ) (hF : (Function.support F).Finite) :
    ∑ m ∈ N.divisors,
        ((ArithmeticFunction.moebius m : ℂ) / ((c * m : ℕ) : ℂ)) *
          ∑ᶠ (k : ℤ) (_ : k ≠ 0),
            F ((k : ℚ) / ((c * m : ℕ) : ℚ)) * quadraticCongruenceRootSumTotal (c * m) h k =
      ∑ r ∈ N.divisors,
          ((ArithmeticFunction.moebius r : ℂ) / ((c * r : ℕ) : ℂ)) *
            (∏ p ∈ (N / r).primeFactors,
              (1 - (quadraticCongruenceRootCountTotal p h : ℂ) / (p : ℂ))) *
            ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r),
              F ((u : ℚ) / ((c * r : ℕ) : ℚ)) *
                quadraticCongruenceRootSumTotal (c * r) h u := by
  classical
  -- the frequency weight attached to a fixed modulus has finite support
  have hsupp : ∀ n : ℕ, n ≠ 0 →
      (Function.support (fun k : ℤ =>
        F ((k : ℚ) / ((n : ℕ) : ℚ)) * quadraticCongruenceRootSumTotal n h k)).Finite := by
    intro n hn
    have hn' : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hinj : Function.Injective (fun k : ℤ => (k : ℚ) / ((n : ℕ) : ℚ)) := by
      intro a b hab
      simp only at hab
      rw [div_eq_div_iff hn' hn'] at hab
      exact_mod_cast mul_right_cancel₀ hn' hab
    refine Set.Finite.subset (Set.Finite.preimage hinj.injOn hF) ?_
    intro k hk
    have : F ((k : ℚ) / ((n : ℕ) : ℚ)) ≠ 0 := by
      intro h0
      exact hk (by simp [h0])
    exact this
  -- step 1: split each unrestricted frequency sum into its causal fibres
  have hstep1 : ∀ m ∈ N.divisors,
      (∑ᶠ (k : ℤ) (_ : k ≠ 0),
          F ((k : ℚ) / ((c * m : ℕ) : ℚ)) * quadraticCongruenceRootSumTotal (c * m) h k) =
        ∑ d ∈ m.divisors,
          ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime (m / d)),
            F (((u * d : ℤ) : ℚ) / ((c * m : ℕ) : ℚ)) *
              quadraticCongruenceRootSumTotal (c * m) h (u * d) := by
    intro m hm
    have hmsq : Squarefree m := hN.squarefree_of_dvd (Nat.dvd_of_mem_divisors hm)
    exact finsum_nonzero_eq_sum_divisors_finsum hmsq _
      (hsupp (c * m) (Nat.mul_ne_zero hc hmsq.ne_zero))
  rw [Finset.sum_congr rfl (fun m hm => by rw [hstep1 m hm, Finset.mul_sum])]
  -- step 2: reindex the divisor pairs
  rw [sum_divisors_sum_divisors_reindex hN.ne_zero
    (fun m d => ((ArithmeticFunction.moebius m : ℂ) / ((c * m : ℕ) : ℂ)) *
      ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime (m / d)),
        F (((u * d : ℤ) : ℚ) / ((c * m : ℕ) : ℚ)) *
          quadraticCongruenceRootSumTotal (c * m) h (u * d))]
  -- step 3: factor each term, then sum the `d` fibre into the Euler product
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrN : r ∣ N := Nat.dvd_of_mem_divisors hr
  have hr0 : r ≠ 0 := (Nat.pos_of_mem_divisors hr).ne'
  have hquot : Squarefree (N / r) := hN.squarefree_of_dvd (Nat.div_dvd_of_dvd hrN)
  have hcr0 : ((c * r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hc hr0)
  have hterm : ∀ d ∈ (N / r).divisors,
      ((ArithmeticFunction.moebius (r * d) : ℂ) / ((c * (r * d) : ℕ) : ℂ)) *
          (∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime ((r * d) / d)),
            F (((u * d : ℤ) : ℚ) / ((c * (r * d) : ℕ) : ℚ)) *
              quadraticCongruenceRootSumTotal (c * (r * d)) h (u * d)) =
        (((ArithmeticFunction.moebius r : ℂ) / ((c * r : ℕ) : ℂ)) *
            ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r),
              F ((u : ℚ) / ((c * r : ℕ) : ℚ)) *
                quadraticCongruenceRootSumTotal (c * r) h u) *
          ((ArithmeticFunction.moebius d : ℂ) *
            ((quadraticCongruenceRootCountTotal d h : ℂ) / (d : ℂ))) := by
    intro d hd
    have hdq : d ∣ N / r := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hrd : r * d ∣ N := (Nat.dvd_div_iff_mul_dvd hrN).mp hdq
    have hrdsq : Squarefree (r * d) := hN.squarefree_of_dvd hrd
    have hcop_rd : r.Coprime d := Nat.coprime_of_squarefree_mul hrdsq
    have hquot_eq : (r * d) / d = r := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)
    have hcm : c.Coprime (r * d) := hcN.coprime_dvd_right hrd
    have hd0' : ((d : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    -- frequency invariance under causal reduction
    have hfreq : ∀ u : ℤ, (((u * d : ℤ) : ℚ) / ((c * (r * d) : ℕ) : ℚ)) =
        ((u : ℚ) / ((c * r : ℕ) : ℚ)) := by
      intro u
      have hdq' : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
      have hcq : ((c : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
      have hrq : ((r : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr0
      push_cast
      field_simp
    -- the anchored root-sum reduction
    have hroot : ∀ u : ℤ,
        quadraticCongruenceRootSumTotal (c * (r * d)) h (u * d) =
          (quadraticCongruenceRootCountTotal d h : ℂ) *
            quadraticCongruenceRootSumTotal (c * r) h u := by
      intro u
      have := quadraticCongruenceRootSumTotal_causalAnchor (c := c) (m := r * d) (d := d)
        hc hrdsq (dvd_mul_left d r) hcm h u
      rwa [hquot_eq] at this
    have hinner : (∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime ((r * d) / d)),
          F (((u * d : ℤ) : ℚ) / ((c * (r * d) : ℕ) : ℚ)) *
            quadraticCongruenceRootSumTotal (c * (r * d)) h (u * d)) =
        (quadraticCongruenceRootCountTotal d h : ℂ) *
          ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r),
            F ((u : ℚ) / ((c * r : ℕ) : ℚ)) *
              quadraticCongruenceRootSumTotal (c * r) h u := by
      rw [hquot_eq, mul_finsum_cond]
      refine finsum_congr fun u => finsum_congr fun _ => ?_
      rw [hfreq u, hroot u]
      ring
    rw [hinner]
    have hmob : (ArithmeticFunction.moebius (r * d) : ℂ) =
        (ArithmeticFunction.moebius r : ℂ) * (ArithmeticFunction.moebius d : ℂ) := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_rd]
      push_cast
      ring
    have hcast : ((c * (r * d) : ℕ) : ℂ) = ((c * r : ℕ) : ℂ) * (d : ℂ) := by
      push_cast
      ring
    rw [hmob, hcast]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    quadraticCongruenceRootDensity_squarefree_euler hquot h]
  ring

end RHTower
