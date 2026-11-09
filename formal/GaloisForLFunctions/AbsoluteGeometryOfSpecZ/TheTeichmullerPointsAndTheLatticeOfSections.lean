import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGhostRingOfTheArithmeticSquare

/-!
# The Teichmüller points and the lattice of sections

The Teichmüller point `[a]` of the arithmetic square is the sequence `[a]_n = aⁿ` (`teichmuller`);
it satisfies the Dwork congruences by Fermat's theorem. `a ↦ [a]` is multiplicative, and on `[a]`
every Frobenius is a power: `F_k [a] = [a]^k`.

* **The constants are the Teichmüller points** (`eq_teichmuller_of_frobenius_eq_pow`): an element
  with `F_p x = x^p` for every prime `p` is `[x_1]`. The elements on which the Frobenius lifts are
  exact are the multiplicative monoid of `ℤ`.
* **The Teichmüller points are linearly independent** (`linearIndependent_teichmuller`), although
  the integers they lift are all multiples of `1`: distinct characters `n ↦ kⁿ` are independent.
* **A lattice of sections with a rank count.** The sections of bidegree `(A, K)` are the
  combinations `Σ_{k ≤ K} c_k [k]` with `|c_k| ≤ A`. There are exactly `(2A + 1)^K` of them
  (`card_image_latticeMap`): the logarithm of the count is `K log(2A + 1)`, linear in the first
  degree `log A` and exponential in the second degree `log K`. Restriction to the graph `Γ_n`
  multiplies the second degree by `n`: `|x_n| ≤ K · A · Kⁿ` (`abs_ghostComponent_latticeMap_le`).
-/

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Fermat's theorem for integers: `p ∣ b^p − b`. -/
theorem prime_dvd_pow_sub_self {p : ℕ} (hp : p.Prime) (b : ℤ) : (p : ℤ) ∣ b ^ p - b := by
  haveI := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

/-- The sequence `n ↦ aⁿ` satisfies the Dwork congruences: `a^{pn} ≡ aⁿ (mod p^{v_p(n)+1})`. -/
theorem isGhost_pow (a : ℤ) : IsGhost fun n : ℕ+ => a ^ (n : ℕ) := by
  intro p hp n
  have hp' : (p : ℕ).Prime := hp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℕ) = (p : ℕ) ^ (n : ℕ).factorization p * m :=
    ⟨_, (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  have h := dvd_sub_pow_of_dvd_sub (prime_dvd_pow_sub_self hp' (a ^ m)) ((n : ℕ).factorization p)
  have e1 : a ^ ((p * n : ℕ+) : ℕ) = ((a ^ m) ^ (p : ℕ)) ^ (p : ℕ) ^ (n : ℕ).factorization p := by
    rw [PNat.mul_coe, ← pow_mul, ← pow_mul]
    congr 1
    nth_rewrite 1 [hm]
    ring
  have e2 : a ^ (n : ℕ) = (a ^ m) ^ (p : ℕ) ^ (n : ℕ).factorization p := by
    rw [← pow_mul]
    congr 1
    nth_rewrite 1 [hm]
    ring
  change ((p : ℕ) : ℤ) ^ ((n : ℕ).factorization p + 1) ∣ a ^ ((p * n : ℕ+) : ℕ) - a ^ (n : ℕ)
  rw [e1, e2]
  exact_mod_cast h

/-- The Teichmüller point `[a]` of the arithmetic square: `[a]_n = aⁿ`. -/
def teichmuller (a : ℤ) : ghostRing := ⟨fun n => a ^ (n : ℕ), isGhost_pow a⟩

@[simp] theorem teichmuller_apply (a : ℤ) (n : ℕ+) : (teichmuller a).1 n = a ^ (n : ℕ) := rfl

@[simp] theorem ghostComponent_teichmuller (a : ℤ) (n : ℕ+) :
    ghostComponent n (teichmuller a) = a ^ (n : ℕ) := rfl

theorem teichmuller_mul (a b : ℤ) : teichmuller (a * b) = teichmuller a * teichmuller b :=
  Subtype.ext (funext fun n => mul_pow a b n)

theorem teichmuller_one : teichmuller 1 = 1 := Subtype.ext (funext fun _ => one_pow _)

/-- On a Teichmüller point the Frobenius is a power: `F_k [a] = [a^k]`. -/
theorem frobenius_teichmuller (k : ℕ+) (a : ℤ) :
    frobenius k (teichmuller a) = teichmuller (a ^ (k : ℕ)) :=
  Subtype.ext (funext fun n => by
    rw [frobenius_apply, teichmuller_apply, teichmuller_apply, PNat.mul_coe, pow_mul])

/-- `F_k [a] = [a]^k`: the Teichmüller points are constants of every Frobenius lift. -/
theorem frobenius_teichmuller_eq_pow (k : ℕ+) (a : ℤ) :
    frobenius k (teichmuller a) = teichmuller a ^ (k : ℕ) := by
  refine Subtype.ext (funext fun n => ?_)
  rw [frobenius_apply, teichmuller_apply, Subring.coe_pow, Pi.pow_apply, teichmuller_apply,
    PNat.mul_coe, ← pow_mul, mul_comm]

/-- **The constants are the Teichmüller points.** If `F_p x = x^p` for every prime `p`, then
`x = [x_1]`. -/
theorem eq_teichmuller_of_frobenius_eq_pow {x : ghostRing}
    (h : ∀ p : ℕ+, p.Prime → frobenius p x = x ^ (p : ℕ)) : x = teichmuller (x.1 1) := by
  have key : ∀ n : ℕ, ∀ N : ℕ+, (N : ℕ) = n → x.1 N = x.1 1 ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro N hN
      by_cases h1 : n = 1
      · have hN1 : N = 1 := PNat.eq (by rw [hN, h1]; rfl)
        rw [hN1, h1, pow_one]
      · -- split off the least prime factor: `x_{pm} = (F_p x)_m = x_m^p`
        have hp := Nat.minFac_prime h1
        obtain ⟨m, hm⟩ := Nat.minFac_dvd n
        have hn0 : 0 < n := hN ▸ N.pos
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · rw [h0, mul_zero] at hm; omega
          · exact h0
        obtain ⟨P, hP⟩ : ∃ P : ℕ+, (P : ℕ) = n.minFac := ⟨⟨_, hp.pos⟩, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M : ℕ+, (M : ℕ) = m := ⟨⟨m, hm0⟩, rfl⟩
        have hNPM : N = P * M := PNat.eq (by rw [PNat.mul_coe, hP, hM, hN]; exact hm)
        have hlt : m < n := by
          have := hp.one_lt
          calc m = 1 * m := (one_mul m).symm
            _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right this hm0
            _ = n := hm.symm
        have hF := congrArg (fun y : ghostRing => y.1 M) (h P (show (P : ℕ).Prime from hP.symm ▸ hp))
        simp only [frobenius_apply, Subring.coe_pow, Pi.pow_apply] at hF
        rw [hNPM, hF, ih m hlt M hM, hP, ← pow_mul]
        congr 1
        rw [mul_comm]; exact hm.symm
  exact Subtype.ext (funext fun N => key N N rfl)

/-! ### Independence -/

/-- **The Teichmüller points are linearly independent**: distinct characters `n ↦ kⁿ` of `(ℕ, +)`
are independent (Dedekind). -/
theorem linearIndependent_teichmuller :
    LinearIndependent ℤ fun k : ℕ+ => teichmuller ((k : ℕ) : ℤ) := by
  have hinj : Function.Injective fun k : ℕ+ => powersHom ℤ (((k : ℕ) : ℤ)) := fun a b hab =>
    PNat.eq (by exact_mod_cast (powersHom ℤ).injective hab)
  have hLI := (linearIndependent_monoidHom (Multiplicative ℕ) ℤ).comp _ hinj
  rw [linearIndependent_iff'] at hLI ⊢
  intro s g hsum k hk
  -- evaluate the relation on the graphs `Γ_{m+1}`: the coefficients `g k · k` kill all characters
  have hg : ∀ j ∈ s, g j * ((j : ℕ) : ℤ) = 0 := by
    refine hLI s (fun j => g j * ((j : ℕ) : ℤ)) (funext fun m => ?_)
    have := congrArg (ghostComponent (Nat.succPNat m.toAdd)) hsum
    rw [map_sum, map_zero] at this
    simp only [map_zsmul, ghostComponent_teichmuller, smul_eq_mul, Nat.succPNat_coe] at this
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, powersHom_apply, smul_eq_mul,
      Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
  have := hg k hk
  rcases mul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd (by exact_mod_cast h0 : (k : ℕ) = 0) k.ne_zero

/-! ### The lattice of sections -/

/-- The section `Σ_{k ≤ K} c_k [k]` with coefficient vector `c`. -/
def latticeMap (K : ℕ) : (Fin K → ℤ) →+ ghostRing where
  toFun c := ∑ k : Fin K, c k • teichmuller (((Nat.succPNat k : ℕ+) : ℕ) : ℤ)
  map_zero' := by simp
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]

theorem latticeMap_apply (K : ℕ) (c : Fin K → ℤ) :
    latticeMap K c = ∑ k : Fin K, c k • teichmuller (((Nat.succPNat k : ℕ+) : ℕ) : ℤ) := rfl

/-- The coefficients of a section are determined by the section. -/
theorem latticeMap_injective (K : ℕ) : Function.Injective (latticeMap K) := by
  have hinj : Function.Injective fun k : Fin K => Nat.succPNat (k : ℕ) := fun a b hab =>
    Fin.ext (Nat.succPNat_injective hab)
  have hLI := linearIndependent_teichmuller.comp _ hinj
  refine (injective_iff_map_eq_zero _).mpr fun c hc => funext fun k => ?_
  exact Fintype.linearIndependent_iff.mp hLI c hc k

/-- The `n`-th component of a section: `x_n = Σ_k c_k (k+1)ⁿ`. -/
theorem ghostComponent_latticeMap (K : ℕ) (c : Fin K → ℤ) (n : ℕ+) :
    ghostComponent n (latticeMap K c) = ∑ k : Fin K, c k * (((k : ℕ) : ℤ) + 1) ^ (n : ℕ) := by
  rw [latticeMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, ghostComponent_teichmuller, smul_eq_mul, Nat.succPNat_coe]
  push_cast
  rfl

open scoped Classical in
/-- **The rank count.** There are exactly `(2A + 1)^K` sections of bidegree `(A, K)`. -/
theorem card_image_latticeMap (A K : ℕ) :
    ((Fintype.piFinset fun _ : Fin K => Finset.Icc (-(A : ℤ)) A).image (latticeMap K)).card =
      (2 * A + 1) ^ K := by
  have hcard : (Finset.Icc (-(A : ℤ)) A).card = 2 * A + 1 := by
    rw [Int.card_Icc]; omega
  rw [Finset.card_image_of_injective _ (latticeMap_injective K), Fintype.card_piFinset]
  simp [hcard]

/-- **Restriction to `Γ_n` multiplies the second degree by `n`**: `|x_n| ≤ K · A · Kⁿ`. -/
theorem abs_ghostComponent_latticeMap_le {A K : ℕ} {c : Fin K → ℤ} (hc : ∀ k, |c k| ≤ A)
    (n : ℕ+) : |ghostComponent n (latticeMap K c)| ≤ (K : ℤ) * (A * (K : ℤ) ^ (n : ℕ)) := by
  rw [ghostComponent_latticeMap]
  calc |∑ k : Fin K, c k * (((k : ℕ) : ℤ) + 1) ^ (n : ℕ)|
      ≤ ∑ k : Fin K, |c k * (((k : ℕ) : ℤ) + 1) ^ (n : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin K, (A : ℤ) * (K : ℤ) ^ (n : ℕ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hk : ((k : ℕ) : ℤ) + 1 ≤ K := by exact_mod_cast k.isLt
        have hk0 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) + 1 := by positivity
        rw [abs_mul, abs_pow, abs_of_nonneg hk0]
        exact mul_le_mul (hc k) (pow_le_pow_left₀ hk0 hk _) (by positivity) (by positivity)
    _ = (K : ℤ) * (A * (K : ℤ) ^ (n : ℕ)) := by simp

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
