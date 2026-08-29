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

/-- Frequencies divisible by `d` reindex the unrestricted frequencies. -/
theorem tsum_dvd_eq_tsum_mul {d : ℕ} (hd : d ≠ 0) (G : ℤ → ℂ) :
    (∑' u : ℤ, (if (d : ℤ) ∣ u then G u else 0)) = ∑' v : ℤ, G (v * d) := by
  classical
  have hd' : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hinj : Function.Injective (fun v : ℤ => v * (d : ℤ)) := fun a b hab =>
    mul_right_cancel₀ hd' hab
  have hsupp : Function.support (fun u : ℤ => if (d : ℤ) ∣ u then G u else 0) ⊆
      Set.range (fun v : ℤ => v * (d : ℤ)) := by
    intro u hu
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hu
    obtain ⟨hdu, -⟩ := hu
    obtain ⟨w, rfl⟩ := hdu
    exact ⟨w, mul_comm _ _⟩
  have h := hinj.tsum_eq (f := fun u : ℤ => if (d : ℤ) ∣ u then G u else 0) hsupp
  rw [← h]
  refine tsum_congr fun v => ?_
  rw [if_pos (dvd_mul_left (d : ℤ) v)]

/-- **Primitivity by Möbius inversion.**  A frequency sum restricted to frequencies coprime to a
modulus is the Möbius transform of the unrestricted sums over its divisor sublattices. -/
theorem tsum_coprime_eq_sum_divisors_moebius {r : ℕ} (hr : r ≠ 0) (G : ℤ → ℂ)
    (hG : Summable G) :
    (∑' u : ℤ, (if (u.natAbs).Coprime r then G u else 0)) =
      ∑ d ∈ r.divisors, ((moebius d : ℤ) : ℂ) * ∑' v : ℤ, G (v * d) := by
  classical
  have hindicator : ∀ d : ℕ, (fun u : ℤ => if (d : ℤ) ∣ u then G u else 0) =
      Set.indicator {u : ℤ | (d : ℤ) ∣ u} G := by
    intro d
    funext u
    rw [Set.indicator_apply]
    rfl
  have hsummable : ∀ d ∈ r.divisors,
      Summable (fun u : ℤ => ((moebius d : ℤ) : ℂ) * (if (d : ℤ) ∣ u then G u else 0)) := by
    intro d _
    refine Summable.mul_left _ ?_
    rw [hindicator d]
    exact hG.indicator _
  have hback : ∀ d ∈ r.divisors,
      ((moebius d : ℤ) : ℂ) * (∑' v : ℤ, G (v * d)) =
        ∑' u : ℤ, ((moebius d : ℤ) : ℂ) * (if (d : ℤ) ∣ u then G u else 0) := by
    intro d hd
    rw [tsum_mul_left, tsum_dvd_eq_tsum_mul (Nat.pos_of_mem_divisors hd).ne' G]
  rw [Finset.sum_congr rfl hback, ← Summable.tsum_finsetSum hsummable]
  refine tsum_congr fun u => ?_
  simp only [mul_ite, mul_zero, ← Finset.sum_filter]
  rw [divisors_filter_dvd_natAbs hr u, ← Finset.sum_mul, sum_divisors_moebius_complex]
  by_cases hcop : (u.natAbs).Coprime r
  · rw [if_pos hcop, if_pos hcop, one_mul]
  · rw [if_neg hcop, if_neg hcop, zero_mul]

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

/-- The nonzero-frequency response term at modulus `q`: the frequency weight at the reduced
frequency times the root response. -/
noncomputable def responseTerm (F : ℚ → ℂ) (q : ℕ) (h : ℤ) (u : ℤ) : ℂ :=
  if u = 0 then 0 else F ((u : ℚ) / (q : ℚ)) * quadraticCongruenceRootSumTotal q h u

@[simp] theorem responseTerm_zero (F : ℚ → ℂ) (q : ℕ) (h : ℤ) :
    responseTerm F q h 0 = 0 := if_pos rfl

theorem responseTerm_of_ne_zero (F : ℚ → ℂ) (q : ℕ) (h : ℤ) {u : ℤ} (hu : u ≠ 0) :
    responseTerm F q h u = F ((u : ℚ) / (q : ℚ)) * quadraticCongruenceRootSumTotal q h u :=
  if_neg hu

/-- The unnormalized anchored response at modulus `q`: the complete nonzero-frequency root sum
against the frequency weight. -/
noncomputable def anchoredResponseRaw (F : ℚ → ℂ) (q : ℕ) (h : ℤ) : ℂ :=
  ∑' u : ℤ, responseTerm F q h u

/-- `A_(q,h)`: the anchored response normalized by the root count. -/
noncomputable def anchoredResponse (F : ℚ → ℂ) (q : ℕ) (h : ℤ) : ℂ :=
  anchoredResponseRaw F q h / (quadraticCongruenceRootCountTotal q h : ℂ)

/-- `B_(c,r,h)`: the anchored response along frequencies primitive on the future remainder `r`,
normalized by the anchor and remainder root counts. -/
noncomputable def primitiveAnchoredResponse (F : ℚ → ℂ) (c r : ℕ) (h : ℤ) : ℂ :=
  (∑' u : ℤ, (if (u.natAbs).Coprime r then responseTerm F (c * r) h u else 0)) /
    ((quadraticCongruenceRootCountTotal c h : ℂ) *
      (quadraticCongruenceRootCountTotal r h : ℂ))

/-- **Reduced-frequency response term.**  Removing a complementary divisor from the modulus and
from the frequency multiplies the response term by the root count of the removed part. -/
theorem responseTerm_mul {c r d : ℕ} (hc : c ≠ 0) (hr : Squarefree r) (hd : d ∣ r)
    (hcr : c.Coprime r) (h : ℤ) (F : ℚ → ℂ) (v : ℤ) :
    responseTerm F (c * r) h (v * d) =
      (quadraticCongruenceRootCountTotal d h : ℂ) * responseTerm F (c * (r / d)) h v := by
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hr.ne_zero hd
  have hq0 : r / d ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hr.ne_zero) hd)
      (Nat.pos_of_ne_zero hd0)
    exact this.ne'
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvd : v * (d : ℤ) ≠ 0 := mul_ne_zero hv (Nat.cast_ne_zero.mpr hd0)
  have hsplit : c * r = c * (r / d) * d := by
    rw [mul_assoc, Nat.div_mul_cancel hd]
  have hfreq : ((v * d : ℤ) : ℚ) / ((c * r : ℕ) : ℚ) = (v : ℚ) / ((c * (r / d) : ℕ) : ℚ) := by
    have hdq : ((d : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    have hcq : ((c : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc
    have hrq : (((r / d : ℕ) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
    rw [hsplit]
    push_cast
    field_simp
  rw [responseTerm_of_ne_zero _ _ _ hvd, responseTerm_of_ne_zero _ _ _ hv, hfreq,
    quadraticCongruenceRootSumTotal_causalAnchor hc hr hd hcr h v]
  ring

/-- The reduced-frequency sublattice sum is the root count of the removed part times the
unrestricted response at the reduced modulus. -/
theorem tsum_responseTerm_mul {c r d : ℕ} (hc : c ≠ 0) (hr : Squarefree r) (hd : d ∣ r)
    (hcr : c.Coprime r) (h : ℤ) (F : ℚ → ℂ) :
    (∑' v : ℤ, responseTerm F (c * r) h (v * d)) =
      (quadraticCongruenceRootCountTotal d h : ℂ) * anchoredResponseRaw F (c * (r / d)) h := by
  rw [anchoredResponseRaw, ← tsum_mul_left]
  exact tsum_congr fun v => responseTerm_mul hc hr hd hcr h F v

/-- **`(CG1)`.**  The primitive anchored response is the Möbius transform of the unrestricted
anchored responses at the reduced moduli. -/
theorem primitiveAnchoredResponse_eq_sum_divisors_moebius
    {c r : ℕ} (hc : c ≠ 0) (hr : Squarefree r) (hcr : c.Coprime r) (h : ℤ)
    (F : ℚ → ℂ) (hF : Summable (responseTerm F (c * r) h)) :
    primitiveAnchoredResponse F c r h =
      ∑ d ∈ r.divisors, ((moebius d : ℤ) : ℂ) * anchoredResponse F (c * (r / d)) h := by
  classical
  have hnum := tsum_coprime_eq_sum_divisors_moebius hr.ne_zero (responseTerm F (c * r) h) hF
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
  rw [tsum_responseTerm_mul hc hr hdr hcr h F, anchoredResponse, hcountcq, hmulcount]
  have hCc : ((quadraticCongruenceRootCountTotal c h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hc h
  have hCq : ((quadraticCongruenceRootCountTotal (r / d) h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hq0 h
  have hCd : ((quadraticCongruenceRootCountTotal d h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hd0 h
  push_cast
  field_simp

/-! ## The complete future Bernoulli average -/

/-- `theta_h(q)`: the local root density of the reducible quadratic. -/
noncomputable def rootDensity (q : ℕ) (h : ℤ) : ℂ :=
  (quadraticCongruenceRootCountTotal q h : ℂ) / (q : ℂ)

/-- On a squarefree modulus the root density is its local Euler product. -/
theorem rootDensity_eq_prod_primeFactors {r : ℕ} (hr : Squarefree r) (h : ℤ) :
    rootDensity r h = ∏ p ∈ r.primeFactors, rootDensity p h := by
  classical
  have hpair : ((r.primeFactors : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq
  have hnz : ∀ p ∈ r.primeFactors, p ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hprod : ∏ p ∈ r.primeFactors, p = r := Nat.prod_primeFactors_of_squarefree hr
  have hcount := quadraticCongruenceRootCountTotal_prod r.primeFactors hpair hnz h
  rw [hprod] at hcount
  rw [rootDensity, hcount]
  simp only [rootDensity, Finset.prod_div_distrib]
  rw [Nat.cast_prod]
  congr 1
  rw [← Nat.cast_prod, hprod]

/-- `V_N(h)`: the local survival Euler product of the packet. -/
noncomputable def survivalProduct (N : ℕ) (h : ℤ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - rootDensity p h)

/-- `w_(N,h)(r)`: the complete Bernoulli weight of a divisor of the packet. -/
noncomputable def bernoulliWeight (N r : ℕ) (h : ℤ) : ℂ :=
  rootDensity r h * survivalProduct (N / r) h

/-- **The complete Bernoulli law of a squarefree packet has total mass one.** -/
theorem sum_divisors_bernoulliWeight {N : ℕ} (hN : Squarefree N) (h : ℤ) :
    ∑ r ∈ N.divisors, bernoulliWeight N r h = 1 := by
  have hcongr : ∀ r ∈ N.divisors, bernoulliWeight N r h =
      (∏ p ∈ r.primeFactors, rootDensity p h) *
        ∏ p ∈ (N / r).primeFactors, (1 - rootDensity p h) := by
    intro r hr
    rw [bernoulliWeight, survivalProduct,
      rootDensity_eq_prod_primeFactors (hN.squarefree_of_dvd (Nat.dvd_of_mem_divisors hr)) h]
  rw [Finset.sum_congr rfl hcongr]
  exact sum_divisors_bernoulliMass hN _

/-- `Eresp_(c,N,h)`: the complete future Bernoulli average of the anchored primitive response. -/
noncomputable def futureResponse (F : ℚ → ℂ) (c N : ℕ) (h : ℤ) : ℂ :=
  ∑ r ∈ N.divisors,
    ((moebius r : ℤ) : ℂ) * bernoulliWeight N r h * primitiveAnchoredResponse F c r h

/-- **`(CG2)`.**  Averaging the primitive anchored responses against the complete Bernoulli
survival law of the future packet collapses them to one signed occupancy response per divisor. -/
theorem futureResponse_eq_sum_divisors
    {c N : ℕ} (hc : c ≠ 0) (hN : Squarefree N) (hcN : c.Coprime N) (h : ℤ)
    (F : ℚ → ℂ) (hF : ∀ q : ℕ, Summable (responseTerm F q h)) :
    futureResponse F c N h =
      ∑ e ∈ N.divisors,
        ((moebius e : ℤ) : ℂ) * rootDensity e h * anchoredResponse F (c * e) h := by
  classical
  have hstep : ∀ r ∈ N.divisors,
      ((moebius r : ℤ) : ℂ) * bernoulliWeight N r h * primitiveAnchoredResponse F c r h =
        ∑ d ∈ r.divisors,
          ((moebius r : ℤ) : ℂ) * bernoulliWeight N r h * ((moebius d : ℤ) : ℂ) *
            anchoredResponse F (c * (r / d)) h := by
    intro r hr
    obtain ⟨hrN, -⟩ := Nat.mem_divisors.1 hr
    have hrsq : Squarefree r := hN.squarefree_of_dvd hrN
    have hcr : c.Coprime r := hcN.coprime_dvd_right hrN
    rw [primitiveAnchoredResponse_eq_sum_divisors_moebius hc hrsq hcr h F (hF (c * r)),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [futureResponse, Finset.sum_congr rfl hstep,
    sum_divisors_sum_divisors_reindex hN.ne_zero
      (fun r d => ((moebius r : ℤ) : ℂ) * bernoulliWeight N r h * ((moebius d : ℤ) : ℂ) *
        anchoredResponse F (c * (r / d)) h)]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨heN, -⟩ := Nat.mem_divisors.1 he
  have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero hN.ne_zero heN
  have hquot : Squarefree (N / e) := hN.squarefree_of_dvd (Nat.div_dvd_of_dvd heN)
  have hterm : ∀ d ∈ (N / e).divisors,
      ((moebius (e * d) : ℤ) : ℂ) * bernoulliWeight N (e * d) h * ((moebius d : ℤ) : ℂ) *
          anchoredResponse F (c * (e * d / d)) h =
        (((moebius e : ℤ) : ℂ) * rootDensity e h * anchoredResponse F (c * e) h) *
          bernoulliWeight (N / e) d h := by
    intro d hd
    obtain ⟨hdq, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hquot.ne_zero hdq
    have hedN : e * d ∣ N := by
      obtain ⟨k, hk⟩ := hdq
      obtain ⟨j, hj⟩ := heN
      refine ⟨k, ?_⟩
      have hje : N / e = j := by rw [hj, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)]
      rw [hj, mul_assoc, ← hk, hje]
    have hedsq : Squarefree (e * d) := hN.squarefree_of_dvd hedN
    have hcop : e.Coprime d := Nat.coprime_of_squarefree_mul hedsq
    have hdsq : Squarefree d := hedsq.squarefree_of_dvd (dvd_mul_left d e)
    have hmoeb : ((moebius (e * d) : ℤ) : ℂ) * ((moebius d : ℤ) : ℂ) =
        ((moebius e : ℤ) : ℂ) := by
      have hmul : (moebius (e * d) : ℤ) = moebius e * moebius d :=
        isMultiplicative_moebius.map_mul_of_coprime hcop
      have hsq : (moebius d : ℤ) ^ 2 = 1 := moebius_sq_eq_one_of_squarefree hdsq
      have : (moebius (e * d) : ℤ) * moebius d = moebius e := by
        rw [hmul, mul_assoc, ← sq, hsq, mul_one]
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
    have hdens : rootDensity (e * d) h = rootDensity e h * rootDensity d h := by
      rw [rootDensity, rootDensity, rootDensity,
        quadraticCongruenceRootCountTotal_mul he0 hd0 hcop h]
      push_cast
      field_simp
    have hdiv : N / (e * d) = (N / e) / d := (Nat.div_div_eq_div_mul N e d).symm
    have hcancel : e * d / d = e := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd0)
    rw [hcancel, bernoulliWeight, bernoulliWeight, hdens, hdiv]
    rw [show ((moebius (e * d) : ℤ) : ℂ) * (rootDensity e h * rootDensity d h *
        survivalProduct (N / e / d) h) * ((moebius d : ℤ) : ℂ) *
        anchoredResponse F (c * e) h
      = (((moebius (e * d) : ℤ) : ℂ) * ((moebius d : ℤ) : ℂ)) * rootDensity e h *
        anchoredResponse F (c * e) h *
        (rootDensity d h * survivalProduct (N / e / d) h) from by ring, hmoeb]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_divisors_bernoulliWeight hquot h,
    mul_one]

/-! ## The protected-anchor cross-colour row -/

/-- A protected-anchor frequency has the same reduced fraction across every crossing colour. -/
theorem protectedAnchorFrequency_eq {q p : ℕ} (hp : p ≠ 0) (v : ℤ) :
    ((v * p : ℤ) : ℚ) / ((q * p : ℕ) : ℚ) = (v : ℚ) / (q : ℚ) := by
  have hpq : ((p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  push_cast
  rcases eq_or_ne ((q : ℕ) : ℚ) 0 with hq0 | hq0
  · rw [hq0]
    simp
  · field_simp

/-- **`(SG10)`.**  The normalized root response at a protected-anchor frequency is literally the
same row for every crossing colour: exposing one more prime in the modulus and the frequency
changes neither the reduced fraction nor the normalized response. -/
theorem protectedAnchorRow_eq {q p : ℕ} (hq : q ≠ 0) (hp : p ≠ 0) (hcop : q.Coprime p)
    (h v : ℤ) :
    quadraticCongruenceRootSumTotal (q * p) h (v * p) /
        (quadraticCongruenceRootCountTotal (q * p) h : ℂ) =
      quadraticCongruenceRootSumTotal q h v /
        (quadraticCongruenceRootCountTotal q h : ℂ) := by
  have halias := quadraticCongruenceRootSumTotal_mul_alias hq hp hcop h v
  have hcount := quadraticCongruenceRootCountTotal_mul hq hp hcop h
  have hCq : ((quadraticCongruenceRootCountTotal q h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hq h
  have hCp : ((quadraticCongruenceRootCountTotal p h : ℕ) : ℂ) ≠ 0 :=
    quadraticCongruenceRootCountTotal_cast_ne_zero hp h
  rw [halias, hcount]
  push_cast
  field_simp

end RHTower
