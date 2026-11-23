import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulWeaklyRegular

/-! Koszul exactness descends from a chart obtained by inverting an
element that is already invertible modulo the weight ideal. -/

noncomputable section

namespace GlobalTheory.WH

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- In the quotient, a power of an element and a left inverse for that
element force the class to vanish. -/
theorem mem_of_pow_smul_mem_of_one_sub_mul_smul_mem
    (P : Submodule R V) {a b : R} {x : V} {N : ℕ}
    (hpow : a ^ N • x ∈ P) (hsub : (1 - a * b) • x ∈ P) : x ∈ P := by
  let q := P.mkQ x
  have hp : a ^ N • q = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hpow
  have hq : (1 - a * b) • q = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsub
  rw [sub_smul, one_smul, sub_eq_zero] at hq
  have hrepl (m : ℕ) : (a * b) ^ m • q = q := by
    induction m with
    | zero => rw [pow_zero, one_smul]
    | succ m hm => rw [pow_succ', mul_smul, hm, ← hq]
  apply (Submodule.Quotient.mk_eq_zero P).mp
  change q = 0
  rw [← hrepl N, mul_pow, mul_comm (a ^ N), mul_smul, hp, smul_zero]

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

private def cochainsAt (P : Type*) [AddCommGroup P] [Module R P] (n : ℤ) :
    Submodule R (Finset ι → P) :=
  Submodule.pi Set.univ fun s => if (s.card : ℤ) = n then ⊤ else ⊥

private theorem mem_cochainsAt {P : Type*} [AddCommGroup P] [Module R P]
    {n : ℤ} {c : Finset ι → P} :
    c ∈ cochainsAt (R := R) P n ↔ ∀ s : Finset ι, (s.card : ℤ) ≠ n → c s = 0 := by
  constructor
  · intro h s hs
    exact (Submodule.mem_bot R).mp (by
      simpa only [if_neg hs] using Submodule.mem_pi.mp h s (Set.mem_univ _))
  · intro h
    refine Submodule.mem_pi.mpr fun s _ => ?_
    split_ifs with hs
    · exact Submodule.mem_top
    · exact (Submodule.mem_bot R).mpr (h s hs)

/-- If each coefficient of the larger lattice has a denominator that
is invertible modulo the weights, exactness on the larger lattice
gives exactness on the original lattice. -/
theorem koszul_exact_of_away_lattice {P Q : Submodule R V} (hPQ : P ≤ Q)
    (r : ι → R) {a b : R} (hab : 1 - a * b ∈ Ideal.span (Set.range r))
    (hden : ∀ x : Q, ∃ N : ℕ, a ^ N • (x : V) ∈ P)
    (n : ℤ)
    (hQ : ∀ c : Finset ι → Q, (∀ s : Finset ι, (s.card : ℤ) ≠ n → c s = 0) →
      koszulDifferential r c = 0 → ∃ y : Finset ι → Q,
        (∀ s : Finset ι, (s.card : ℤ) ≠ n - 1 → y s = 0) ∧ koszulDifferential r y = c)
    (c : Finset ι → P) (hc : ∀ s : Finset ι, (s.card : ℤ) ≠ n → c s = 0)
    (hD : koszulDifferential r c = 0) :
    ∃ y : Finset ι → P, (∀ s : Finset ι, (s.card : ℤ) ≠ n - 1 → y s = 0) ∧
      koszulDifferential r y = c := by
  let f : P →ₗ[R] Q := Submodule.inclusion hPQ
  let c' (s : Finset ι) := f (c s)
  have hc' (s : Finset ι) (hs : (s.card : ℤ) ≠ n) : c' s = 0 := by
    rw [show c' s = f (c s) from rfl, hc s hs, map_zero]
  have hd' : koszulDifferential r c' = 0 := by
    funext s
    have he := congrArg (fun z : Finset ι → P => f (z s)) hD
    simpa only [koszulDifferential_apply, map_sum, map_zsmul, map_smul, c',
      Pi.zero_apply, map_zero] using he
  obtain ⟨y, hy, hdy⟩ := hQ c' hc' hd'
  choose N hN using fun s => hden (y s)
  let m : ℕ := ∑ s, N s
  have hm (s : Finset ι) : a ^ m • (y s : V) ∈ P := by
    have hs : N s ≤ m := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    rw [← Nat.sub_add_cancel hs, pow_add, mul_smul]
    exact P.smul_mem _ (hN s)
  let z (s : Finset ι) : P := ⟨a ^ m • (y s : V), hm s⟩
  have hz (s : Finset ι) (hs : (s.card : ℤ) ≠ n - 1) : z s = 0 := by
    apply Subtype.ext
    change a ^ m • (y s : V) = 0
    rw [hy s hs, Submodule.coe_zero, smul_zero]
  have hfz : (fun s => f (z s)) = a ^ m • y := by
    funext s
    exact Subtype.ext rfl
  have hdz : koszulDifferential r z = a ^ m • c := by
    funext s
    apply Submodule.inclusion_injective hPQ
    have he : koszulDifferential r (fun t => f (z t)) s =
        f (koszulDifferential r z s) := by
      simp only [koszulDifferential_apply, map_sum, map_zsmul, map_smul]
    rw [hfz, map_smul, hdy] at he
    rw [← he, Pi.smul_apply, Pi.smul_apply, map_smul]
  obtain ⟨u, hu, hdu⟩ := exists_koszul_primitive_smul r hc hD hab
  let B := (cochainsAt P (n - 1)).map (koszulDifferential r)
  have hpow : a ^ m • c ∈ B := ⟨z, mem_cochainsAt.mpr hz, hdz⟩
  have hsub : (1 - a * b) • c ∈ B := ⟨u, mem_cochainsAt.mpr hu, hdu⟩
  obtain ⟨v, hv, hdv⟩ := (mem_of_pow_smul_mem_of_one_sub_mul_smul_mem B hpow hsub : c ∈ B)
  exact ⟨v, mem_cochainsAt.mp hv, hdv⟩

end GlobalTheory.WH
