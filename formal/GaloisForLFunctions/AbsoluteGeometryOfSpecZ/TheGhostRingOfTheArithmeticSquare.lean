import Mathlib

/-!
# The ghost ring of the arithmetic square

In the geometry where descent to `𝔽₁` is a commuting family of Frobenius lifts, the product
`Spec ℤ ×_{𝔽₁} Spec ℤ` is the spectrum of the big Witt vectors `W(ℤ)`. In ghost coordinates `W(ℤ)`
is the ring `𝒢` of integer sequences `(x_n)_{n ≥ 1}` satisfying the **Dwork congruences**

  `x_{pn} ≡ x_n  (mod p^{v_p(n)+1})`  for all primes `p` and all `n ≥ 1`   (`IsGhost`, `ghostRing`).

The component `x ↦ x_n` is the graph `Γ_n` of the Frobenius of degree `n`, a copy of `Spec ℤ`; the
congruences glue the graphs along the primes.

* `F_k`, `(F_k x)_n = x_{kn}`, is a ring endomorphism of `𝒢` (`frobenius`), and `V_k`,
  `(V_k x)_n = k x_{n/k}` for `k ∣ n` and `0` otherwise, is an additive endomorphism
  (`verschiebung`); `F_k F_l = F_{kl}`, `F_k V_k = k`, and for coprime `m, n`
  `F_{gn} V_{gm} = g · V_m F_n`: a Frobenius composed with its transpose is its degree.
* The orbits `e_d = V_d 1`, `(e_d)_n = d·[d ∣ n]`, satisfy
  `e_d e_{d'} = gcd(d, d') e_{lcm(d, d')}` (`orbit_mul_orbit`).
* **Necklace decomposition** (`isGhost_iff_exists_necklace`): a sequence lies in `𝒢` iff
  `x_n = Σ_{d ∣ n} d b_d` with integers `b_d`, the number of closed points of degree `d`; the `b_d`
  are unique (`necklace_unique`). The proof subtracts the orbits of the proper divisors of `n`; the
  congruences at the primes dividing `n` then give `n ∣ x_n`.
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-! ### Arithmetic lemmas -/

/-- A divisor of `p n` that does not divide `n` is divisible by `p^{v_p(n)+1}`. -/
theorem pow_succ_factorization_dvd {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : k ∣ p * n)
    (h' : ¬ k ∣ n) : p ^ (n.factorization p + 1) ∣ k := by
  have hk : k ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff] at h
    exact (mul_ne_zero hp.ne_zero hn) h
  rw [hp.pow_dvd_iff_le_factorization hk]
  by_contra hlt
  refine h' ((Nat.factorization_le_iff_dvd hk hn).mp fun q => ?_)
  have hle := (Nat.factorization_le_iff_dvd hk (mul_ne_zero hp.ne_zero hn)).mpr h q
  rw [Nat.factorization_mul hp.ne_zero hn, hp.factorization, Finsupp.add_apply] at hle
  by_cases hq : q = p
  · subst hq; omega
  · rwa [Finsupp.single_eq_of_ne hq, zero_add] at hle

/-- An integer divisible by `p^{v_p(n)}` for every prime `p` is divisible by `n`. -/
theorem natCast_dvd_of_forall_prime_pow {n : ℕ} (hn : n ≠ 0) {a : ℤ}
    (h : ∀ p : ℕ, p.Prime → ((p : ℤ) ^ n.factorization p) ∣ a) : (n : ℤ) ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero _
  rw [Int.natCast_dvd]
  have ha' : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  refine (Nat.factorization_le_iff_dvd hn ha').mp fun q => ?_
  by_cases hq : q.Prime
  · have := h q hq
    rw [← Nat.cast_pow, Int.natCast_dvd] at this
    exact (hq.pow_dvd_iff_le_factorization ha').mp this
  · rw [Nat.factorization_eq_zero_of_not_prime n hq]; exact Nat.zero_le _

/-! ### The ghost ring -/

/-- **Dwork congruences**: `p^{v_p(n)+1} ∣ x_{pn} − x_n` for all primes `p` and all `n`. -/
def IsGhost (x : ℕ+ → ℤ) : Prop :=
  ∀ p : ℕ+, p.Prime → ∀ n : ℕ+,
    ((p : ℕ) : ℤ) ^ ((n : ℕ).factorization p + 1) ∣ x (p * n) - x n

/-- The coordinate ring of the arithmetic square `Spec ℤ ×_{𝔽₁} Spec ℤ`, in ghost coordinates. -/
def ghostRing : Subring (ℕ+ → ℤ) where
  carrier := {x | IsGhost x}
  mul_mem' := by
    intro x y hx hy p hp n
    have h : (x * y) (p * n) - (x * y) n =
        x (p * n) * (y (p * n) - y n) + y n * (x (p * n) - x n) := by
      simp only [Pi.mul_apply]; ring
    rw [h]
    exact dvd_add ((hy p hp n).mul_left _) ((hx p hp n).mul_left _)
  one_mem' := fun p _ n => by simp
  add_mem' := by
    intro x y hx hy p hp n
    have h : (x + y) (p * n) - (x + y) n = (x (p * n) - x n) + (y (p * n) - y n) := by
      simp only [Pi.add_apply]; ring
    rw [h]
    exact dvd_add (hx p hp n) (hy p hp n)
  zero_mem' := fun p _ n => by simp
  neg_mem' := by
    intro x hx p hp n
    have h : (-x) (p * n) - (-x) n = -(x (p * n) - x n) := by
      simp only [Pi.neg_apply]; ring
    rw [h]
    exact (dvd_neg).mpr (hx p hp n)

theorem mem_ghostRing {x : ℕ+ → ℤ} : x ∈ ghostRing ↔ IsGhost x := Iff.rfl

/-- The graph `Γ_n`: the `n`-th ghost component, a ring homomorphism `𝒢 → ℤ`. -/
def ghostComponent (n : ℕ+) : ghostRing →+* ℤ :=
  (Pi.evalRingHom (fun _ : ℕ+ => ℤ) n).comp ghostRing.subtype

@[simp] theorem ghostComponent_apply (n : ℕ+) (x : ghostRing) : ghostComponent n x = x.1 n := rfl

/-- Two elements of `𝒢` with the same ghost components are equal: the graphs cover the square. -/
theorem ghostRing_ext {x y : ghostRing} (h : ∀ n, ghostComponent n x = ghostComponent n y) :
    x = y := Subtype.ext (funext h)

/-! ### Frobenius -/

/-- The Frobenius `F_k` on sequences: `(F_k x)_n = x_{kn}`. -/
def frobeniusFun (k : ℕ+) : (ℕ+ → ℤ) →+* (ℕ+ → ℤ) where
  toFun x := fun n => x (k * n)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem frobeniusFun_apply (k : ℕ+) (x : ℕ+ → ℤ) (n : ℕ+) :
    frobeniusFun k x n = x (k * n) := rfl

theorem isGhost_frobeniusFun (k : ℕ+) {x : ℕ+ → ℤ} (hx : IsGhost x) :
    IsGhost (frobeniusFun k x) := by
  intro p hp n
  have h := hx p hp (k * n)
  rw [← mul_left_comm] at h
  refine (pow_dvd_pow _ (Nat.succ_le_succ ?_)).trans h
  rw [PNat.mul_coe, Nat.factorization_mul k.ne_zero n.ne_zero, Finsupp.add_apply]
  exact Nat.le_add_left _ _

/-- The Frobenius `F_k` of the arithmetic square. -/
def frobenius (k : ℕ+) : ghostRing →+* ghostRing :=
  (frobeniusFun k).restrict ghostRing ghostRing fun _ hx => isGhost_frobeniusFun k hx

@[simp] theorem frobenius_apply (k : ℕ+) (x : ghostRing) (n : ℕ+) :
    (frobenius k x).1 n = x.1 (k * n) := rfl

/-- `F_k F_l = F_{kl}`. -/
theorem frobenius_frobenius (k l : ℕ+) (x : ghostRing) :
    frobenius k (frobenius l x) = frobenius (l * k) x :=
  Subtype.ext (funext fun n => by simp [mul_assoc])

@[simp] theorem frobenius_one (x : ghostRing) : frobenius 1 x = x :=
  Subtype.ext (funext fun n => by simp)

/-- `Γ_n` is the diagonal composed with `F_n`. -/
theorem ghostComponent_frobenius (k n : ℕ+) (x : ghostRing) :
    ghostComponent n (frobenius k x) = ghostComponent (k * n) x := rfl

/-! ### Verschiebung -/

/-- The Verschiebung `V_k` on sequences: `(V_k x)_n = k x_{n/k}` if `k ∣ n`, else `0`. -/
def verschiebungFun (k : ℕ+) : (ℕ+ → ℤ) →+ (ℕ+ → ℤ) where
  toFun x := fun n => if (k : ℕ) ∣ n then ((k : ℕ) : ℤ) * x (PNat.divExact n k) else 0
  map_zero' := by funext n; simp
  map_add' x y := by
    funext n
    by_cases h : (k : ℕ) ∣ n <;> simp [h, mul_add]

theorem verschiebungFun_apply (k : ℕ+) (x : ℕ+ → ℤ) (n : ℕ+) :
    verschiebungFun k x n =
      if (k : ℕ) ∣ n then ((k : ℕ) : ℤ) * x (PNat.divExact n k) else 0 := rfl

/-- `(V_k x)_{kn} = k x_n`. -/
theorem verschiebungFun_mul (k : ℕ+) (x : ℕ+ → ℤ) (n : ℕ+) :
    verschiebungFun k x (k * n) = ((k : ℕ) : ℤ) * x n := by
  have hd : k ∣ k * n := dvd_mul_right k n
  rw [verschiebungFun_apply, if_pos (PNat.dvd_iff.mp hd)]
  congr 2
  exact mul_left_cancel (a := k) (PNat.mul_div_exact hd)

theorem verschiebungFun_of_not_dvd (k : ℕ+) (x : ℕ+ → ℤ) {n : ℕ+} (h : ¬ (k : ℕ) ∣ n) :
    verschiebungFun k x n = 0 := by
  rw [verschiebungFun_apply, if_neg h]

theorem isGhost_verschiebungFun (k : ℕ+) {x : ℕ+ → ℤ} (hx : IsGhost x) :
    IsGhost (verschiebungFun k x) := by
  intro p hp n
  by_cases hkn : (k : ℕ) ∣ n
  · -- `n = k n'`: the difference is `k (x_{pn'} − x_{n'})`
    obtain ⟨n', rfl⟩ := PNat.dvd_iff.mpr hkn
    rw [← mul_left_comm, verschiebungFun_mul, verschiebungFun_mul, ← mul_sub, PNat.mul_coe,
      Nat.factorization_mul k.ne_zero n'.ne_zero, Finsupp.add_apply, add_assoc, pow_add]
    refine mul_dvd_mul ?_ (hx p hp n')
    exact_mod_cast Nat.ordProj_dvd (k : ℕ) (p : ℕ)
  · rw [verschiebungFun_of_not_dvd k x hkn, sub_zero]
    by_cases hkpn : (k : ℕ) ∣ (p * n : ℕ+)
    · -- `k ∣ pn`, `k ∤ n`: then `p^{v_p(n)+1} ∣ k`
      rw [verschiebungFun_apply, if_pos hkpn]
      refine Dvd.dvd.mul_right ?_ _
      rw [PNat.mul_coe] at hkpn
      exact_mod_cast pow_succ_factorization_dvd hp n.ne_zero hkpn hkn
    · rw [verschiebungFun_of_not_dvd k x hkpn]
      exact dvd_zero _

/-- The Verschiebung `V_k` of the arithmetic square. -/
def verschiebung (k : ℕ+) : ghostRing →+ ghostRing where
  toFun x := ⟨verschiebungFun k x.1, isGhost_verschiebungFun k x.2⟩
  map_zero' := Subtype.ext (map_zero (verschiebungFun k))
  map_add' x y := Subtype.ext (map_add (verschiebungFun k) x.1 y.1)

theorem verschiebung_apply (k : ℕ+) (x : ghostRing) (n : ℕ+) :
    (verschiebung k x).1 n =
      if (k : ℕ) ∣ n then ((k : ℕ) : ℤ) * x.1 (PNat.divExact n k) else 0 := rfl

/-- **`F_k V_k = k`**: a Frobenius composed with its transpose is its degree. -/
theorem frobenius_verschiebung (k : ℕ+) (x : ghostRing) :
    frobenius k (verschiebung k x) = ((k : ℕ) : ℤ) • x :=
  Subtype.ext (funext fun n => by
    rw [frobenius_apply]
    exact (verschiebungFun_mul k x.1 n).trans (by simp))

/-- **`F_{gn} V_{gm} = g V_m F_n`** for coprime `m, n`: the common factor of the two degrees comes out
as a multiplicity. -/
theorem frobenius_verschiebung_of_coprime (g : ℕ+) {m n : ℕ+} (h : Nat.Coprime m n)
    (x : ghostRing) :
    frobenius (g * n) (verschiebung (g * m) x) =
      ((g : ℕ) : ℤ) • verschiebung m (frobenius n x) := by
  refine Subtype.ext (funext fun j => ?_)
  rw [frobenius_apply]
  change verschiebungFun (g * m) x.1 (g * n * j) =
    ((g : ℕ) : ℤ) • verschiebungFun m (frobeniusFun n x.1) j
  by_cases hmj : (m : ℕ) ∣ j
  · obtain ⟨j', rfl⟩ := PNat.dvd_iff.mpr hmj
    rw [verschiebungFun_mul, show g * n * (m * j') = g * m * (n * j') by
      simp only [mul_assoc, mul_left_comm], verschiebungFun_mul, PNat.mul_coe]
    simp [mul_assoc]
  · rw [verschiebungFun_of_not_dvd m _ hmj, smul_zero]
    refine verschiebungFun_of_not_dvd _ _ fun hd => hmj ?_
    have h1 : (g : ℕ) * m ∣ g * (n * j) := by
      simpa [PNat.mul_coe, mul_assoc] using hd
    exact h.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left g.pos h1)

/-! ### Orbits -/

/-- The orbit `e_d = V_d 1`: the free cyclic orbit of length `d`, with `d` fixed points of `F_n`
when `d ∣ n` and none otherwise. -/
def orbit (d : ℕ+) : ghostRing := verschiebung d 1

@[simp] theorem orbit_apply (d n : ℕ+) :
    (orbit d).1 n = if (d : ℕ) ∣ n then ((d : ℕ) : ℤ) else 0 := by
  change verschiebungFun d 1 n = _
  rw [verschiebungFun_apply]
  simp

/-- `e_d e_{d'} = gcd(d, d') e_{lcm(d, d')}`: a product of two orbits is `gcd` orbits of length `lcm`. -/
theorem orbit_mul_orbit (d d' : ℕ+) :
    orbit d * orbit d' = ((Nat.gcd d d' : ℕ) : ℤ) • orbit (PNat.lcm d d') := by
  refine Subtype.ext (funext fun n => ?_)
  have hl : ((PNat.lcm d d' : ℕ+) : ℕ) ∣ n ↔ (d : ℕ) ∣ n ∧ (d' : ℕ) ∣ n := by
    rw [PNat.lcm_coe]
    exact Nat.lcm_dvd_iff
  change (orbit d).1 n * (orbit d').1 n = ((Nat.gcd d d' : ℕ) : ℤ) • (orbit (PNat.lcm d d')).1 n
  rw [orbit_apply, orbit_apply, orbit_apply]
  by_cases h1 : (d : ℕ) ∣ n
  · by_cases h2 : (d' : ℕ) ∣ n
    · rw [if_pos h1, if_pos h2, if_pos (hl.mpr ⟨h1, h2⟩), PNat.lcm_coe, smul_eq_mul]
      exact_mod_cast (Nat.gcd_mul_lcm d d').symm
    · rw [if_neg h2, if_neg fun h => h2 (hl.mp h).2]; simp
  · rw [if_neg h1, if_neg fun h => h1 (hl.mp h).1]; simp

/-! ### The necklace decomposition -/

/-- The sequence on `ℕ` extending a sequence on `ℕ+` by `0` at `0`. -/
def toNat (x : ℕ+ → ℤ) (n : ℕ) : ℤ := if h : 0 < n then x ⟨n, h⟩ else 0

@[simp] theorem toNat_coe (x : ℕ+ → ℤ) (n : ℕ+) : toNat x n = x n := by
  simp [toNat, n.pos]

/-- The Dwork congruences in terms of natural indices. -/
theorem IsGhost.toNat_dvd {x : ℕ+ → ℤ} (hx : IsGhost x) {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (p : ℤ) ^ (n.factorization p + 1) ∣ toNat x (p * n) - toNat x n := by
  have h := hx ⟨p, hp.pos⟩ hp ⟨n, Nat.pos_of_ne_zero hn⟩
  have e1 : toNat x (p * n) = x (⟨p, hp.pos⟩ * ⟨n, Nat.pos_of_ne_zero hn⟩) := by
    rw [← toNat_coe]; rfl
  have e2 : toNat x n = x ⟨n, Nat.pos_of_ne_zero hn⟩ := by
    rw [← toNat_coe]; rfl
  rw [e1, e2]
  exact h

/-- Necklace coordinates of a sequence, by recursion over the proper divisors:
`n b_n = y_n − Σ_{d ∣ n, d < n} d b_d`. -/
noncomputable def necklace (y : ℕ → ℤ) (n : ℕ) : ℤ :=
  (y n - ∑ d ∈ n.properDivisors.attach, (d.1 : ℤ) * necklace y d.1) / n
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

theorem necklace_eq (y : ℕ → ℤ) (n : ℕ) :
    necklace y n = (y n - ∑ d ∈ n.properDivisors, (d : ℤ) * necklace y d) / n := by
  rw [necklace, Finset.sum_attach n.properDivisors fun d => (d : ℤ) * necklace y d]

/-- **Necklace decomposition, existence.** A sequence satisfying the Dwork congruences is the sum of
its necklace coordinates over the divisors. -/
theorem IsGhost.eq_sum_necklace {x : ℕ+ → ℤ} (hx : IsGhost x) (n : ℕ) (hn : n ≠ 0) :
    toNat x n = ∑ d ∈ n.divisors, (d : ℤ) * necklace (toNat x) d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    set b := necklace (toNat x) with hb
    set S := ∑ d ∈ n.properDivisors, (d : ℤ) * b d with hS
    -- the congruences at the primes dividing `n` give `n ∣ x_n − S`
    have hdvd : (n : ℤ) ∣ toNat x n - S := by
      refine natCast_dvd_of_forall_prime_pow hn fun p hp => ?_
      by_cases hpn : p ∣ n
      · obtain ⟨n', rfl⟩ := hpn
        have hn' : n' ≠ 0 := fun h => hn (by rw [h, mul_zero])
        have hlt : n' < p * n' := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hn') hp.one_lt
        have hfac : (p * n').factorization p = n'.factorization p + 1 := by
          rw [Nat.factorization_mul hp.ne_zero hn', Finsupp.add_apply, hp.factorization,
            Finsupp.single_eq_same, add_comm]
        have hsub : n'.divisors ⊆ (p * n').properDivisors := fun d hd => by
          rw [Nat.mem_properDivisors]
          have hd' := Nat.mem_divisors.mp hd
          exact ⟨hd'.1.mul_left p, (Nat.le_of_dvd (Nat.pos_of_ne_zero hn') hd'.1).trans_lt hlt⟩
        have hsplit : toNat x (p * n') - S =
            (toNat x (p * n') - toNat x n') -
              ∑ d ∈ (p * n').properDivisors \ n'.divisors, (d : ℤ) * b d := by
          rw [ih n' hlt hn', hS, ← Finset.sum_sdiff hsub]; ring
        rw [hsplit, hfac]
        refine dvd_sub (hx.toNat_dvd hp hn') (Finset.dvd_sum fun d hd => Dvd.dvd.mul_right ?_ _)
        obtain ⟨hd1, hd2⟩ := Finset.mem_sdiff.mp hd
        have hd3 : ¬ d ∣ n' := fun h => hd2 (Nat.mem_divisors.mpr ⟨h, hn'⟩)
        exact_mod_cast pow_succ_factorization_dvd hp hn' (Nat.mem_properDivisors.mp hd1).1 hd3
      · rw [Nat.factorization_eq_zero_of_not_dvd hpn, pow_zero]; exact one_dvd _
    have hbn : (n : ℤ) * b n = toNat x n - S := by
      rw [hb, necklace_eq, ← hb, ← hS]
      exact Int.mul_ediv_cancel' hdvd
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self, ← hS, hbn]
    ring

/-- **Necklace decomposition, converse.** A sequence of the form `Σ_{d ∣ n} d b_d` satisfies the
Dwork congruences. -/
theorem isGhost_of_necklace {x : ℕ+ → ℤ} {b : ℕ → ℤ}
    (h : ∀ n : ℕ+, x n = ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * b d) : IsGhost x := by
  intro p hp n
  have hsub : (n : ℕ).divisors ⊆ ((p : ℕ) * n).divisors :=
    Nat.divisors_subset_of_dvd (mul_ne_zero p.ne_zero n.ne_zero) (dvd_mul_left _ _)
  rw [h, h, PNat.mul_coe, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  refine Finset.dvd_sum fun d hd => Dvd.dvd.mul_right ?_ _
  obtain ⟨hd1, hd2⟩ := Finset.mem_sdiff.mp hd
  have hd3 : ¬ d ∣ (n : ℕ) := fun h => hd2 (Nat.mem_divisors.mpr ⟨h, n.ne_zero⟩)
  exact_mod_cast pow_succ_factorization_dvd hp n.ne_zero (Nat.mem_divisors.mp hd1).1 hd3

/-- **Necklace decomposition.** The arithmetic square consists of the sequences
`x_n = Σ_{d ∣ n} d b_d` with integer `b_d`. -/
theorem isGhost_iff_exists_necklace (x : ℕ+ → ℤ) :
    IsGhost x ↔ ∃ b : ℕ → ℤ, ∀ n : ℕ+, x n = ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * b d :=
  ⟨fun hx => ⟨necklace (toNat x), fun n => by
    rw [← toNat_coe x n]; exact hx.eq_sum_necklace n n.ne_zero⟩,
   fun ⟨_, h⟩ => isGhost_of_necklace h⟩

/-- **The necklace coordinates are unique.** -/
theorem necklace_unique {b b' : ℕ → ℤ}
    (h : ∀ n : ℕ, n ≠ 0 →
      ∑ d ∈ n.divisors, (d : ℤ) * b d = ∑ d ∈ n.divisors, (d : ℤ) * b' d)
    (n : ℕ) (hn : n ≠ 0) : b n = b' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 := h n hn
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self,
      Nat.sum_divisors_eq_sum_properDivisors_add_self] at h1
    have h2 : ∑ d ∈ n.properDivisors, (d : ℤ) * b d = ∑ d ∈ n.properDivisors, (d : ℤ) * b' d :=
      Finset.sum_congr rfl fun d hd => by
        have hd' := Nat.mem_properDivisors.mp hd
        rw [ih d hd'.2 (Nat.pos_of_dvd_of_pos hd'.1 (Nat.pos_of_ne_zero hn)).ne']
    rw [h2] at h1
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn) (add_left_cancel h1)

/-- The number of closed points of degree `d` of an element of the arithmetic square. -/
noncomputable def coord (x : ghostRing) (d : ℕ) : ℤ := necklace (toNat x.1) d

/-- `x_n = Σ_{d ∣ n} d b_d(x)`. -/
theorem ghostComponent_eq_sum_coord (x : ghostRing) (n : ℕ+) :
    ghostComponent n x = ∑ d ∈ (n : ℕ).divisors, (d : ℤ) * coord x d := by
  rw [ghostComponent_apply, ← toNat_coe x.1 n]
  exact x.2.eq_sum_necklace n n.ne_zero

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
