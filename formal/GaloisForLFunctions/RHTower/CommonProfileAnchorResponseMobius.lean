import GaloisForLFunctions.RHTower.CausallyAnchoredFutureAliasRegrouping

/-!
# The anchored primitive response and its Möbius reduction

For a causal anchor `c` coprime to a squarefree future packet, the frequency sum restricted to
frequencies primitive along the future remainder is the Möbius transform of the unrestricted
anchored responses.  Averaging that transform against the complete Bernoulli survival law of the
packet collapses it to a single signed occupancy response.

The three inputs are the coprimality indicator as a Möbius divisor sum, reduced-frequency alias
lifting, and multiplicativity of the quadratic root count.
-/

open scoped BigOperators
open ArithmeticFunction

namespace RHTower

/-! ## Divisors of a squarefree number -/

/-- **Squarefree divisor/powerset transfer.**  Summing over the divisors of a squarefree number is
summing over the subsets of its prime support. -/
theorem sum_divisors_squarefree_eq_sum_powerset {M : Type*} [AddCommMonoid M] {m : ℕ}
    (hm : Squarefree m) (f : ℕ → M) :
    ∑ d ∈ m.divisors, f d = ∑ t ∈ m.primeFactors.powerset, f (∏ p ∈ t, p) := by
  classical
  refine (Finset.sum_nbij' (fun t => ∏ p ∈ t, p) (fun d => d.primeFactors) ?_ ?_ ?_ ?_ ?_).symm
  · intro t ht
    rw [Finset.mem_powerset] at ht
    refine Nat.mem_divisors.2 ⟨?_, hm.ne_zero⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ m.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ ht
      _ = m := Nat.prod_primeFactors_of_squarefree hm
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Finset.mem_powerset.2 (Nat.primeFactors_mono hd.1 hd.2)
  · intro t ht
    rw [Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  · intro d hd
    rw [Nat.mem_divisors] at hd
    exact Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hd.1)
  · intro t _
    rfl

/-- The complementary divisor of a squarefree number has the complementary prime support. -/
theorem primeFactors_div_of_squarefree {m : ℕ} (hm : Squarefree m) {t : Finset ℕ}
    (ht : t ⊆ m.primeFactors) :
    (m / ∏ p ∈ t, p).primeFactors = m.primeFactors \ t := by
  classical
  have hprod : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hm
  have hsplit : (∏ p ∈ t, p) * (∏ p ∈ m.primeFactors \ t, p) = m := by
    rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset ht, hprod]
  have hdvd : (∏ p ∈ t, p) ∣ m := ⟨_, hsplit.symm⟩
  have hne : (∏ p ∈ t, p) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
    exact (Nat.prime_of_mem_primeFactors (ht hp)).ne_zero
  have hquot : m / ∏ p ∈ t, p = ∏ p ∈ m.primeFactors \ t, p :=
    Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hne) (hsplit.symm.trans (mul_comm _ _))
  rw [hquot]
  exact Nat.primeFactors_prod fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.1 hp).1

/-- **Complete Bernoulli mass.**  Over a squarefree packet the active weight of one divisor times
the survival weight of its complement sums to one. -/
theorem sum_divisors_bernoulliMass {R : Type*} [CommRing R] {m : ℕ} (hm : Squarefree m)
    (θ : ℕ → R) :
    ∑ d ∈ m.divisors,
        (∏ p ∈ d.primeFactors, θ p) * ∏ p ∈ (m / d).primeFactors, (1 - θ p) = 1 := by
  classical
  rw [sum_divisors_squarefree_eq_sum_powerset hm]
  have hcongr : ∀ t ∈ m.primeFactors.powerset,
      (∏ p ∈ (∏ q ∈ t, q).primeFactors, θ p) *
          ∏ p ∈ (m / ∏ q ∈ t, q).primeFactors, (1 - θ p) =
        (∏ p ∈ t, θ p) * ∏ p ∈ m.primeFactors \ t, (1 - θ p) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (ht hp),
      primeFactors_div_of_squarefree hm ht]
  rw [Finset.sum_congr rfl hcongr, ← Finset.prod_add]
  simp

/-! ## Möbius expansion of the primitivity restriction -/

/-- The Möbius sum over the divisors of an integer is the unit indicator. -/
theorem sum_divisors_moebius_complex (n : ℕ) :
    ∑ d ∈ n.divisors, ((moebius d : ℤ) : ℂ) = if n = 1 then 1 else 0 := by
  have h : ∑ i ∈ n.divisors, moebius i = if n = 1 then 1 else 0 := by
    have h0 := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h0
    exact h0
  have hc := congrArg (fun z : ℤ => (z : ℂ)) h
  push_cast at hc
  rw [hc]

/-- The divisors of a modulus dividing a frequency are the divisors of their greatest common
divisor. -/
theorem divisors_filter_dvd_natAbs {r : ℕ} (hr : r ≠ 0) (u : ℤ) :
    Finset.filter (fun d : ℕ => (d : ℤ) ∣ u) r.divisors = (Nat.gcd u.natAbs r).divisors := by
  classical
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Int.natCast_dvd, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨hdr, -⟩, hdu⟩
    exact ⟨⟨hdu, hdr⟩, fun h0 => hr (Nat.eq_zero_of_gcd_eq_zero_right h0)⟩
  · rintro ⟨⟨hdu, hdr⟩, -⟩
    exact ⟨⟨hdr, hr⟩, hdu⟩

/-- Frequencies divisible by `d` reindex the unrestricted nonzero frequencies. -/
theorem finsum_nonzero_mul_eq_finsum_dvd {M : Type*} [AddCommMonoid M] {d : ℕ} (hd : d ≠ 0)
    (G : ℤ → M) :
    (∑ᶠ (v : ℤ) (_ : v ≠ 0), G (v * d)) =
      ∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (d : ℤ) ∣ u), G u := by
  have hd' : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hinj : Set.InjOn (fun v : ℤ => v * (d : ℤ)) {v : ℤ | v ≠ 0} := by
    intro a _ b _ hab
    exact mul_right_cancel₀ hd' hab
  have hset : (fun v : ℤ => v * (d : ℤ)) '' {v : ℤ | v ≠ 0} =
      {u : ℤ | u ≠ 0 ∧ (d : ℤ) ∣ u} := by
    ext u
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨mul_ne_zero hv hd', dvd_mul_left _ _⟩
    · rintro ⟨hu, w, rfl⟩
      refine ⟨w, ?_, mul_comm _ _⟩
      intro h0
      exact hu (by rw [h0, mul_zero])
  have himg := finsum_mem_image (f := G) hinj
  rw [hset] at himg
  exact himg.symm

/-- **Primitivity by Möbius inversion.**  A frequency sum restricted to frequencies coprime to a
modulus is the Möbius transform of the unrestricted sums over its divisor sublattices. -/
theorem finsum_coprime_eq_sum_divisors_moebius {r : ℕ} (hr : r ≠ 0) (G : ℤ → ℂ)
    (hG : (Function.support G).Finite) :
    (∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r), G u) =
      ∑ d ∈ r.divisors, ((moebius d : ℤ) : ℂ) * ∑ᶠ (v : ℤ) (_ : v ≠ 0), G (v * d) := by
  classical
  set A : Set ℤ := {u : ℤ | u ≠ 0} with hA
  set Cop : Set ℤ := {u : ℤ | (u.natAbs).Coprime r} with hCop
  have hfin : ∀ (S : Set ℤ) (z : ℂ),
      Function.HasFiniteSupport (fun u : ℤ => z * S.indicator G u) := by
    intro S z
    refine hG.subset fun u hu => ?_
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    have hne : S.indicator G u ≠ 0 := hu.2
    exact fun h0 => hne (by simp [Set.indicator_apply, h0])
  have hlhs : (∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r), G u) =
      ∑ᶠ (u : ℤ), (A ∩ Cop).indicator G u := finsum_mem_def _ _
  have hrhs : ∀ d ∈ r.divisors,
      ((moebius d : ℤ) : ℂ) * (∑ᶠ (v : ℤ) (_ : v ≠ 0), G (v * d)) =
        ∑ᶠ (u : ℤ), ((moebius d : ℤ) : ℂ) *
          (A ∩ {u : ℤ | (d : ℤ) ∣ u}).indicator G u := by
    intro d hd
    have hset : (∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (d : ℤ) ∣ u), G u) =
        ∑ᶠ (u : ℤ), (A ∩ {u : ℤ | (d : ℤ) ∣ u}).indicator G u := finsum_mem_def _ _
    rw [finsum_nonzero_mul_eq_finsum_dvd (Nat.pos_of_mem_divisors hd).ne' G, hset, mul_finsum]
  rw [hlhs, Finset.sum_congr rfl hrhs,
    ← finsum_sum_comm r.divisors
      (fun (u : ℤ) (d : ℕ) => ((moebius d : ℤ) : ℂ) *
        (A ∩ {u : ℤ | (d : ℤ) ∣ u}).indicator G u)
      (fun d _ => hfin _ _)]
  refine finsum_congr fun u => ?_
  by_cases hu : u = 0
  · subst hu
    have hzero : ∀ d : ℕ, (A ∩ {v : ℤ | (d : ℤ) ∣ v}).indicator G 0 = 0 := by
      intro d
      rw [Set.indicator_of_notMem]
      simp [hA]
    simp only [hzero, mul_zero, Finset.sum_const_zero]
    rw [Set.indicator_of_notMem]
    simp [hA]
  · have hind : ∀ d : ℕ, (A ∩ {v : ℤ | (d : ℤ) ∣ v}).indicator G u =
        if (d : ℤ) ∣ u then G u else 0 := by
      intro d
      by_cases hd : (d : ℤ) ∣ u
      · rw [Set.indicator_of_mem
          (show u ∈ A ∩ {v : ℤ | (d : ℤ) ∣ v} from ⟨hu, hd⟩) G, if_pos hd]
      · rw [Set.indicator_of_notMem (by simp [hd]), if_neg hd]
    simp only [hind, mul_ite, mul_zero, ← Finset.sum_filter]
    rw [divisors_filter_dvd_natAbs hr u, ← Finset.sum_mul, sum_divisors_moebius_complex]
    by_cases hcop : (u.natAbs).Coprime r
    · rw [if_pos hcop, one_mul,
        Set.indicator_of_mem (show u ∈ A ∩ Cop from ⟨hu, hcop⟩) G]
    · rw [if_neg hcop, zero_mul, Set.indicator_of_notMem (by simp [hCop, hcop])]

/-! ## The anchored responses -/

/-- Positivity of the totalized quadratic root count at a nondegenerate modulus. -/
theorem quadraticCongruenceRootCountTotal_pos {n : ℕ} (hn : n ≠ 0) (h : ℤ) :
    0 < quadraticCongruenceRootCountTotal n h := by
  letI : NeZero n := ⟨hn⟩
  rw [quadraticCongruenceRootCountTotal_of_ne_zero hn]
  exact quadraticCongruenceRootCount_pos n h

theorem quadraticCongruenceRootCountTotal_cast_ne_zero {n : ℕ} (hn : n ≠ 0) (h : ℤ) :
    ((quadraticCongruenceRootCountTotal n h : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (quadraticCongruenceRootCountTotal_pos hn h).ne'

/-- The unnormalized anchored response at modulus `q`: the complete nonzero-frequency root sum
against a frequency weight. -/
noncomputable def anchoredResponseRaw (F : ℚ → ℂ) (q : ℕ) (h : ℤ) : ℂ :=
  ∑ᶠ (u : ℤ) (_ : u ≠ 0), F ((u : ℚ) / (q : ℚ)) * quadraticCongruenceRootSumTotal q h u

/-- `A_(q,h)`: the anchored response normalized by the root count. -/
noncomputable def anchoredResponse (F : ℚ → ℂ) (q : ℕ) (h : ℤ) : ℂ :=
  anchoredResponseRaw F q h / (quadraticCongruenceRootCountTotal q h : ℂ)

/-- `B_(c,r,h)`: the anchored response along frequencies primitive on the future remainder `r`,
normalized by the anchor and remainder root counts. -/
noncomputable def primitiveAnchoredResponse (F : ℚ → ℂ) (c r : ℕ) (h : ℤ) : ℂ :=
  (∑ᶠ (u : ℤ) (_ : u ≠ 0 ∧ (u.natAbs).Coprime r),
      F ((u : ℚ) / ((c * r : ℕ) : ℚ)) * quadraticCongruenceRootSumTotal (c * r) h u) /
    ((quadraticCongruenceRootCountTotal c h : ℂ) *
      (quadraticCongruenceRootCountTotal r h : ℂ))

/-- The frequency weight attached to a fixed nondegenerate modulus has finite support. -/
theorem support_frequencyWeight_finite {n : ℕ} (hn : n ≠ 0) (h : ℤ) {F : ℚ → ℂ}
    (hF : (Function.support F).Finite) :
    (Function.support (fun u : ℤ =>
      F ((u : ℚ) / (n : ℚ)) * quadraticCongruenceRootSumTotal n h u)).Finite := by
  have hn' : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hinj : Function.Injective (fun u : ℤ => (u : ℚ) / ((n : ℕ) : ℚ)) := by
    intro a b hab
    simp only at hab
    rw [div_eq_div_iff hn' hn'] at hab
    exact_mod_cast mul_right_cancel₀ hn' hab
  refine Set.Finite.subset (Set.Finite.preimage hinj.injOn hF) ?_
  intro u hu
  have hne : F ((u : ℚ) / ((n : ℕ) : ℚ)) ≠ 0 := by
    intro h0
    exact hu (by simp [h0])
  exact hne

/-- Removing a complementary divisor from the modulus and the frequency leaves the root count of
the removed part times the unrestricted response at the reduced modulus. -/
theorem finsum_alias_shift {c r d : ℕ} (hc : c ≠ 0) (hr : Squarefree r) (hd : d ∣ r)
    (hcr : c.Coprime r) (h : ℤ) (F : ℚ → ℂ) :
    (∑ᶠ (v : ℤ) (_ : v ≠ 0),
        F (((v * d : ℤ) : ℚ) / ((c * r : ℕ) : ℚ)) *
          quadraticCongruenceRootSumTotal (c * r) h (v * d)) =
      (quadraticCongruenceRootCountTotal d h : ℂ) * anchoredResponseRaw F (c * (r / d)) h := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hr.ne_zero hd
  have hsplit : c * r = c * (r / d) * d := by
    rw [mul_assoc, Nat.div_mul_cancel hd]
  have hfreq : ∀ v : ℤ,
      ((v * d : ℤ) : ℚ) / ((c * r : ℕ) : ℚ) = (v : ℚ) / ((c * (r / d) : ℕ) : ℚ) := by
    intro v
    rw [hsplit]
    push_cast
    rw [mul_comm ((c : ℚ) * ((r / d : ℕ) : ℚ)) (d : ℚ), ← div_div,
      mul_div_assoc, mul_comm (v : ℚ) (d : ℚ), mul_div_assoc,
      div_self (Nat.cast_ne_zero.mpr hd0 : (d : ℚ) ≠ 0), mul_one]
  have hterm : ∀ v : ℤ,
      F (((v * d : ℤ) : ℚ) / ((c * r : ℕ) : ℚ)) *
          quadraticCongruenceRootSumTotal (c * r) h (v * d) =
        (quadraticCongruenceRootCountTotal d h : ℂ) *
          (F ((v : ℚ) / ((c * (r / d) : ℕ) : ℚ)) *
            quadraticCongruenceRootSumTotal (c * (r / d)) h v) := by
    intro v
    rw [hfreq v, quadraticCongruenceRootSumTotal_causalAnchor hc hr hd hcr h v]
    ring
  rw [finsum_congr fun v => finsum_congr fun _ => hterm v]
  rw [anchoredResponseRaw, mul_finsum_cond]

/-- **`(CG1)`.**  The primitive anchored response is the Möbius transform of the unrestricted
anchored responses at the reduced moduli. -/
theorem primitiveAnchoredResponse_eq_sum_divisors_moebius
    {c r : ℕ} (hc : c ≠ 0) (hr : Squarefree r) (hcr : c.Coprime r) (h : ℤ)
    (F : ℚ → ℂ) (hF : (Function.support F).Finite) :
    primitiveAnchoredResponse F c r h =
      ∑ d ∈ r.divisors, ((moebius d : ℤ) : ℂ) * anchoredResponse F (c * (r / d)) h := by
  classical
  have hcr0 : c * r ≠ 0 := Nat.mul_ne_zero hc hr.ne_zero
  have hnum := finsum_coprime_eq_sum_divisors_moebius hr.ne_zero
    (fun u : ℤ => F ((u : ℚ) / ((c * r : ℕ) : ℚ)) * quadraticCongruenceRootSumTotal (c * r) h u)
    (support_frequencyWeight_finite hcr0 h hF)
  rw [primitiveAnchoredResponse, hnum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdr, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hr.ne_zero hdr
  have hq0 : r / d ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr.ne_zero) hdr)
      (Nat.pos_of_ne_zero hd0)
    exact this.ne'
  have hcq : c.Coprime (r / d) := hcr.coprime_dvd_right (Nat.div_dvd_of_dvd hdr)
  have hmulcount : quadraticCongruenceRootCountTotal r h =
      quadraticCongruenceRootCountTotal (r / d) h * quadraticCongruenceRootCountTotal d h := by
    have hqd : (r / d).Coprime d := by
      apply Nat.coprime_of_squarefree_mul
      rwa [Nat.div_mul_cancel hdr]
    have := quadraticCongruenceRootCountTotal_mul hq0 hd0 hqd h
    rwa [Nat.div_mul_cancel hdr] at this
  have hcountcq : quadraticCongruenceRootCountTotal (c * (r / d)) h =
      quadraticCongruenceRootCountTotal c h * quadraticCongruenceRootCountTotal (r / d) h :=
    quadraticCongruenceRootCountTotal_mul hc hq0 hcq h
  have hshift := finsum_alias_shift hc hr hdr hcr h F
  rw [hshift, anchoredResponse, hcountcq, hmulcount]
  have hCc : ((quadraticCongruenceRootCountTotal c h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hc h
  have hCq : ((quadraticCongruenceRootCountTotal (r / d) h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hq0 h
  have hCd : ((quadraticCongruenceRootCountTotal d h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hd0 h
  push_cast
  field_simp

end RHTower
