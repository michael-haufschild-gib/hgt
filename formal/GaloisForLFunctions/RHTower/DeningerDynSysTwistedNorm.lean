import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Lemma 5.3: the twisted norm quotient is a prime-to-`νν'` torsion group

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 5.3.

For an automorphism `σ` of an abelian group `G` with divisible underlying group and finite
`σ`-orbits, and natural numbers `ν' < ν`, the *twisted norm* `y ↦ y^ν σ(y)^{-ν'}` has image `H`,
and every class of `G / H` is represented by an element `ζ` with `ζ^{ν^i} = ζ^{ν'^i}` for some
`i ≥ 1`.  Those `ζ` are exactly the roots of unity of order prime to `νν'`.
-/

namespace RHTower

open Finset

variable {G : Type*} [CommGroup G]

/-! ## Roots of unity killed by `ν^i - ν'^i` -/

/-- **Deninger, Lemma 5.3, (50).**  An element of finite order satisfies `ζ^{ν^i} = ζ^{ν'^i}` for
some `i ≥ 1` exactly when its order is prime to `νν'`. -/
theorem deningerPow_eq_pow_iff_coprime {ν ν' : ℕ} (hcop : Nat.Coprime ν ν')
    (ζ : G) (hζ : IsOfFinOrder ζ) :
    (∃ i : ℕ, 0 < i ∧ ζ ^ (ν ^ i) = ζ ^ (ν' ^ i)) ↔ Nat.Coprime (orderOf ζ) (ν * ν') := by
  have hpos : 0 < orderOf ζ := hζ.orderOf_pos
  constructor
  · rintro ⟨i, hi, hpow⟩
    have hmod : ν ^ i ≡ ν' ^ i [MOD orderOf ζ] := pow_eq_pow_iff_modEq.1 hpow
    have hdvdZ : ((orderOf ζ : ℤ)) ∣ ((ν' ^ i : ℕ) : ℤ) - ((ν ^ i : ℕ) : ℤ) := hmod.dvd
    have hcop1 : Nat.Coprime (orderOf ζ) ν := by
      rw [Nat.Coprime, Nat.eq_one_iff_not_exists_prime_dvd]
      rintro l hl hdvd
      have hlN : l ∣ orderOf ζ := hdvd.trans (Nat.gcd_dvd_left _ _)
      have hlν : l ∣ ν := hdvd.trans (Nat.gcd_dvd_right _ _)
      have hlνi : (l : ℤ) ∣ ((ν ^ i : ℕ) : ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.2 (dvd_pow hlν (by omega))
      have hlZ : (l : ℤ) ∣ ((ν' ^ i : ℕ) : ℤ) := by
        have h1 : (l : ℤ) ∣ ((ν' ^ i : ℕ) : ℤ) - ((ν ^ i : ℕ) : ℤ) :=
          (Int.natCast_dvd_natCast.2 hlN).trans hdvdZ
        simpa using dvd_add h1 hlνi
      have hlν' : l ∣ ν' := hl.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 hlZ)
      have : l ∣ 1 := hcop ▸ Nat.dvd_gcd hlν hlν'
      exact hl.one_lt.ne' (Nat.dvd_one.1 this)
    have hcop2 : Nat.Coprime (orderOf ζ) ν' := by
      rw [Nat.Coprime, Nat.eq_one_iff_not_exists_prime_dvd]
      rintro l hl hdvd
      have hlN : l ∣ orderOf ζ := hdvd.trans (Nat.gcd_dvd_left _ _)
      have hlν' : l ∣ ν' := hdvd.trans (Nat.gcd_dvd_right _ _)
      have hlν'i : (l : ℤ) ∣ ((ν' ^ i : ℕ) : ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.2 (dvd_pow hlν' (by omega))
      have hlZ : (l : ℤ) ∣ ((ν ^ i : ℕ) : ℤ) := by
        have h1 : (l : ℤ) ∣ ((ν' ^ i : ℕ) : ℤ) - ((ν ^ i : ℕ) : ℤ) :=
          (Int.natCast_dvd_natCast.2 hlN).trans hdvdZ
        have h2 : (l : ℤ) ∣ ((ν ^ i : ℕ) : ℤ) - ((ν' ^ i : ℕ) : ℤ) := by
          have hneg := dvd_neg.2 h1
          simpa [neg_sub] using hneg
        simpa using dvd_add h2 hlν'i
      have hlν : l ∣ ν := hl.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 hlZ)
      have : l ∣ 1 := hcop ▸ Nat.dvd_gcd hlν hlν'
      exact hl.one_lt.ne' (Nat.dvd_one.1 this)
    exact hcop1.mul_right hcop2
  · intro h
    refine ⟨(orderOf ζ).totient, Nat.totient_pos.2 hpos, ?_⟩
    refine pow_eq_pow_iff_modEq.2 ?_
    have hcν : Nat.Coprime ν (orderOf ζ) :=
      (Nat.Coprime.coprime_dvd_right (dvd_mul_right ν ν') h).symm
    have hcν' : Nat.Coprime ν' (orderOf ζ) :=
      (Nat.Coprime.coprime_dvd_right (dvd_mul_left ν' ν) h).symm
    have h1 : ν ^ (orderOf ζ).totient ≡ 1 [MOD orderOf ζ] := Nat.ModEq.pow_totient hcν
    have h2 : ν' ^ (orderOf ζ).totient ≡ 1 [MOD orderOf ζ] := Nat.ModEq.pow_totient hcν'
    exact h1.trans h2.symm

/-! ## The twisted norm and the surjectivity -/

/-- **Deninger, Lemma 5.3.**  The twisted norm `y ↦ y^ν σ (y)^{-ν'}`. -/
def deningerTwistHom (σ : G ≃* G) (ν ν' : ℕ) : G →* G where
  toFun y := y ^ ν * (σ y ^ ν')⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_pow, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

@[simp] theorem deningerTwistHom_apply (σ : G ≃* G) (ν ν' : ℕ) (y : G) :
    deningerTwistHom σ ν ν' y = y ^ ν * (σ y ^ ν')⁻¹ := rfl

/-- The telescoping identity `(z^ω)^ν σ (z^ω)^{-ν'} = z^{ν^i} σ^i (z)^{-ν'^i}` for
`ω = Σ_{α<i} ν^{i-1-α} ν'^α σ^α`, which is Deninger's factorisation
`ν^i - ν'^i σ^i = ω (ν - ν' σ)` in the group ring. -/
theorem deningerTwistHom_prod (σ : G ≃* G) (ν ν' : ℕ) (z : G) {i : ℕ} (hi : 0 < i) :
    deningerTwistHom σ ν ν'
        (∏ α ∈ Finset.range i, ((σ : G → G)^[α] z) ^ (ν ^ (i - 1 - α) * ν' ^ α))
      = z ^ ν ^ i * (((σ : G → G)^[i] z) ^ ν' ^ i)⁻¹ := by
  set g : ℕ → G := fun β => ((σ : G → G)^[β] z) ^ (ν ^ (i - β) * ν' ^ β) with hg
  set y : G := ∏ α ∈ Finset.range i, ((σ : G → G)^[α] z) ^ (ν ^ (i - 1 - α) * ν' ^ α) with hy
  have hy1 : y ^ ν = ∏ α ∈ Finset.range i, g α := by
    rw [hy, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun α hα => ?_
    rw [Finset.mem_range] at hα
    rw [← pow_mul]
    have hstep : ν ^ (i - 1 - α) * ν' ^ α * ν = ν ^ (i - α) * ν' ^ α := by
      have hidx : i - 1 - α + 1 = i - α := by omega
      calc ν ^ (i - 1 - α) * ν' ^ α * ν = ν ^ (i - 1 - α) * ν * ν' ^ α := by ring
        _ = ν ^ (i - 1 - α + 1) * ν' ^ α := by rw [pow_succ]
        _ = ν ^ (i - α) * ν' ^ α := by rw [hidx]
    rw [hstep]
  have hσy : σ y = ∏ α ∈ Finset.range i,
      ((σ : G → G)^[α + 1] z) ^ (ν ^ (i - 1 - α) * ν' ^ α) := by
    rw [hy, map_prod]
    refine Finset.prod_congr rfl fun α _ => ?_
    rw [map_pow, ← Function.iterate_succ_apply' (σ : G → G) α z]
  have hy2 : (σ y) ^ ν' = ∏ β ∈ Finset.Ico 1 (i + 1), g β := by
    rw [hσy, ← Finset.prod_pow, Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.prod_congr rfl fun α hα => ?_
    rw [Finset.mem_range] at hα
    rw [← pow_mul]
    have hidx : 1 + α = α + 1 := by omega
    rw [hidx, hg]
    have hstep : ν ^ (i - 1 - α) * ν' ^ α * ν' = ν ^ (i - (α + 1)) * ν' ^ (α + 1) := by
      have h1 : i - 1 - α = i - (α + 1) := by omega
      rw [h1, pow_succ]
      ring
    rw [hstep]
  have hsplit1 : ∏ α ∈ Finset.range i, g α = g 0 * ∏ α ∈ Finset.Ico 1 i, g α := by
    rw [Finset.range_eq_Ico]
    exact Finset.prod_eq_prod_Ico_succ_bot hi g
  have hsplit2 : ∏ β ∈ Finset.Ico 1 (i + 1), g β = (∏ β ∈ Finset.Ico 1 i, g β) * g i :=
    Finset.prod_Ico_succ_top hi g
  have hg0 : g 0 = z ^ ν ^ i := by simp [hg]
  have hgi : g i = ((σ : G → G)^[i] z) ^ ν' ^ i := by simp [hg]
  rw [deningerTwistHom_apply, hy1, hy2, hsplit1, hsplit2, hg0, hgi, mul_inv]
  rw [mul_comm (∏ β ∈ Finset.Ico 1 i, g β)⁻¹ (((σ : G → G)^[i] z) ^ ν' ^ i)⁻¹]
  rw [← mul_assoc, mul_assoc (z ^ ν ^ i), mul_comm (∏ β ∈ Finset.Ico 1 i, g β)]
  rw [← mul_assoc, mul_assoc (z ^ ν ^ i * (((σ : G → G)^[i] z) ^ ν' ^ i)⁻¹)]
  simp

/-- **Deninger, Lemma 5.3.**  If `G` is divisible and every `σ`-orbit is finite, then every class
of `G` modulo the image of the twisted norm is represented by an element `ζ` satisfying
`ζ^{ν^i} = ζ^{ν'^i}` for some `i ≥ 1`. -/
theorem deningerTwistHom_range_exists (σ : G ≃* G)
    (hdiv : ∀ (c : G) (n : ℕ), 0 < n → ∃ z : G, z ^ n = c)
    (hfin : ∀ c : G, ∃ i : ℕ, 0 < i ∧ (σ : G → G)^[i] c = c)
    {ν ν' : ℕ} (hlt : ν' < ν) (c : G) :
    ∃ (i : ℕ) (ζ : G), 0 < i ∧ ζ ^ ν ^ i = ζ ^ ν' ^ i ∧
      c * ζ⁻¹ ∈ (deningerTwistHom σ ν ν').range := by
  obtain ⟨i, hi, hci⟩ := hfin c
  have hmn : ν' ^ i < ν ^ i := Nat.pow_lt_pow_left hlt (by omega)
  obtain ⟨z, hz⟩ := hdiv c (ν ^ i - ν' ^ i) (by omega)
  set w : G := (σ : G → G)^[i] z with hwdef
  have hw : w ^ (ν ^ i - ν' ^ i) = z ^ (ν ^ i - ν' ^ i) := by
    rw [hwdef, ← iterate_map_pow σ i z, hz, hci]
  set η : G := w * z⁻¹ with hηdef
  have hη : η ^ (ν ^ i - ν' ^ i) = 1 := by
    rw [hηdef, mul_pow, inv_pow, hw, mul_inv_cancel]
  refine ⟨i, η ^ ν' ^ i, hi, ?_, ?_⟩
  · have hkey : (η ^ ν' ^ i) ^ (ν ^ i - ν' ^ i) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hη, one_pow]
    have hsum : ν ^ i - ν' ^ i + ν' ^ i = ν ^ i := by omega
    calc (η ^ ν' ^ i) ^ ν ^ i
        = (η ^ ν' ^ i) ^ (ν ^ i - ν' ^ i + ν' ^ i) := by rw [hsum]
      _ = (η ^ ν' ^ i) ^ (ν ^ i - ν' ^ i) * (η ^ ν' ^ i) ^ ν' ^ i := by rw [pow_add]
      _ = (η ^ ν' ^ i) ^ ν' ^ i := by rw [hkey, one_mul]
  · refine ⟨∏ α ∈ Finset.range i, ((σ : G → G)^[α] z) ^ (ν ^ (i - 1 - α) * ν' ^ α), ?_⟩
    rw [deningerTwistHom_prod σ ν ν' z hi]
    have hwη : w = η * z := by rw [hηdef]; group
    have hzsplit : z ^ ν ^ i = z ^ (ν ^ i - ν' ^ i) * z ^ ν' ^ i := by
      rw [← pow_add]
      congr 1
      omega
    rw [← hwdef, hwη, mul_pow, mul_inv, hzsplit, hz]
    rw [mul_comm ((η ^ ν' ^ i)⁻¹) ((z ^ ν' ^ i)⁻¹), ← mul_assoc, mul_assoc c]
    rw [mul_inv_cancel, mul_one]

/-- **Deninger, Lemma 5.3, the "in particular".**  Modulo the image of the twisted norm, every
element of `G` is killed by an exponent prime to `νν'`. -/
theorem deningerTwistHom_quotient_torsion (σ : G ≃* G)
    (hdiv : ∀ (c : G) (n : ℕ), 0 < n → ∃ z : G, z ^ n = c)
    (hfin : ∀ c : G, ∃ i : ℕ, 0 < i ∧ (σ : G → G)^[i] c = c)
    {ν ν' : ℕ} (hcop : Nat.Coprime ν ν') (hlt : ν' < ν) (c : G) :
    ∃ n : ℕ, 0 < n ∧ Nat.Coprime n (ν * ν') ∧ c ^ n ∈ (deningerTwistHom σ ν ν').range := by
  obtain ⟨i, ζ, hi, hζ, hmem⟩ := deningerTwistHom_range_exists σ hdiv hfin hlt c
  have hmn : ν' ^ i < ν ^ i := Nat.pow_lt_pow_left hlt (by omega)
  have hone : ζ ^ (ν ^ i - ν' ^ i) = 1 := by
    have hsum : ν ^ i - ν' ^ i + ν' ^ i = ν ^ i := by omega
    have hstep : ζ ^ (ν ^ i - ν' ^ i) * ζ ^ ν' ^ i = 1 * ζ ^ ν' ^ i := by
      rw [← pow_add, hsum, hζ, one_mul]
    exact mul_right_cancel hstep
  have hfo : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨ν ^ i - ν' ^ i, by omega, hone⟩
  have hcopn : Nat.Coprime (orderOf ζ) (ν * ν') :=
    (deningerPow_eq_pow_iff_coprime hcop ζ hfo).1 ⟨i, hi, hζ⟩
  refine ⟨orderOf ζ, hfo.orderOf_pos, hcopn, ?_⟩
  have hcn : c ^ orderOf ζ = (c * ζ⁻¹) ^ orderOf ζ := by
    rw [mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one]
  rw [hcn]
  exact pow_mem hmem _

/-- The unit group of an algebraically closed field is divisible, which is the hypothesis `hdiv`
of Lemma 5.3 in Deninger's setting. -/
theorem deningerUnits_divisible {κ : Type*} [Field κ] [IsAlgClosed κ] (c : κˣ) (n : ℕ)
    (hn : 0 < n) : ∃ z : κˣ, z ^ n = c := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (c : κ) hn
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hw
    exact c.ne_zero hw.symm
  refine ⟨Units.mk0 w hw0, ?_⟩
  ext
  simpa using hw

end RHTower
