import GaloisForLFunctions.AdelicKreinGeometry.TheWitnessComplementIsPositive
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanPlacePaysTheTowerDeficit
import GaloisForLFunctions.HeckeKreinToeplitz.LogarithmicCharactersAndTheArithmeticIndexFormula
import GaloisForLFunctions.HeckeKreinToeplitz.TheMarginIsTheWidthOfTheIndexOneWindow

/-!
# No fixed counterterm makes the prime kernel Pontryagin

Weil's prime kernel on the Hecke lattice `ℚ_{>0}` is `P(u) = Λ(u)u^{−1/2}` on prime powers
`u = p^k`, the same on their inverses, and `0` elsewhere; on the atoms `1, …, N` its Gram matrix is
the atomic prime form `P_N` (`gram_primeLatticeKernel`). The matched local Hodge index says that
`P_N − (log N − γ − η)` has one positive direction on every window `[1, N]`
(`RenormalizedArithmeticPotentialTheory`). This file shows that the counterterm cannot be frozen.

* **Escape by two new primes** (`primeLatticeKernel_escape`). For finite families `x, y`, the
  translate by `t = PQ`, with `P ≠ Q` primes above every numerator and denominator, puts both
  primes into the numerator of every `x_a⁻¹ t y_b`: it is neither `1` nor a prime power nor the
  inverse of one, so the kernel vanishes there.
* **Infinite index for every counterterm** (`negIndex_counterterm_sub_primeLatticeKernel`). For every
  real `D`, the kernel `D·δ₁ − P` on `ℚ_{>0}` is Hermitian and escapes, so its index is `0` or
  `∞`; the truncated pole vector `n^{−1/2}` on `[1, N]` has `P_N`-energy at least
  `(log N − γ − η)` times its mass, which exceeds `D` for large `N`. Hence `κ(D·δ₁ − P) = ∞`.

The finite-window statement survives only with the running counterterm `log N − γ`: the matched
prime form has no Pontryagin limit on the Hecke lattice at any fixed renormalization. The infinite
assembly of the local Hodge indices is obstructed at the horizon, and the archimedean place must
supply a counterterm that grows with it.
-/

open Complex Finset Filter
open scoped ComplexConjugate ArithmeticFunction.vonMangoldt
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticEffectivityTheory (weilPrimeKernel)
open GaloisForLFunctions.ArithmeticElectrostatics (atomicWeilForm weilPrimeKernel_comm)
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (truncPole
  eventually_atomicWeilForm_truncPole_ge)

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

local notation "γ" => Real.eulerMascheroniConstant

/-- Weil's prime kernel on the Hecke lattice, read on the reduced fraction `u = num/den`. -/
def primeLatticeKernel (u : HeckeLattice) : ℂ :=
  (weilPrimeKernel (u : ℚ).den (u : ℚ).num.natAbs : ℂ)

/-- The counterterm `D` at the identity minus the prime kernel. -/
def countertermKernel (D : ℝ) (u : HeckeLattice) : ℂ :=
  (if (u : ℚ) = 1 then (D : ℂ) else 0) - primeLatticeKernel u

/-- On a reduced fraction the prime kernel is the atomic one. -/
theorem weilPrimeKernel_div (m n : ℕ) (hm : 0 < m) :
    weilPrimeKernel ((n : ℚ) / m).den ((n : ℚ) / m).num.natAbs = weilPrimeKernel m n := by
  set g := Nat.gcd m n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have hcop : Nat.Coprime (n / g) (m / g) := by
    have := Nat.coprime_div_gcd_div_gcd (m := n) (n := m) (by rw [Nat.gcd_comm]; exact hg)
    rwa [Nat.gcd_comm] at this
  have hm' : 0 < m / g := Nat.div_pos (Nat.gcd_le_left n hm) hg
  have h1 : ((m / g : ℕ) : ℚ) * g = m := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have h2 : ((n / g : ℕ) : ℚ) * g = n := by exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right m n)
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hq : (n : ℚ) / m = ((((n / g : ℕ) : ℤ) : ℚ)) / ((((m / g : ℕ) : ℤ) : ℚ)) := by
    rw [Int.cast_natCast, Int.cast_natCast, ← h1, ← h2, mul_div_mul_right _ _ hg']
  have hcopZ : Nat.Coprime (((n / g : ℕ) : ℤ)).natAbs (((m / g : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast]; exact hcop
  have hden := Rat.den_div_eq_of_coprime (by exact_mod_cast hm') hcopZ
  have hnum := Rat.num_div_eq_of_coprime (by exact_mod_cast hm') hcopZ
  have hden' : ((((n / g : ℕ) : ℤ) : ℚ) / (((m / g : ℕ) : ℤ) : ℚ)).den = m / g := by
    exact_mod_cast hden
  have hnum' : ((((n / g : ℕ) : ℤ) : ℚ) / (((m / g : ℕ) : ℤ) : ℚ)).num.natAbs = n / g := by
    rw [hnum, Int.natAbs_natCast]
  rw [hq, hden', hnum', ← HeckeKreinToeplitz.weilPrimeKernel_mul_left hg (m / g) (n / g),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left m n), Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)]

/-- The prime kernel is real and symmetric under inversion. -/
theorem isHermKernel_primeLatticeKernel : IsHermKernel primeLatticeKernel := fun u => by
  have hq : (0 : ℚ) < u := u.2
  have hinv : ((u⁻¹ : HeckeLattice) : ℚ) = ((u : ℚ).den : ℤ) / (u : ℚ).num := by
    show (u : ℚ)⁻¹ = _
    conv_lhs => rw [← Rat.num_div_den (u : ℚ)]
    rw [inv_div]
    push_cast
    rfl
  have hnum : 0 < (u : ℚ).num := Rat.num_pos.mpr hq
  have hcop : Nat.Coprime (((u : ℚ).den : ℤ)).natAbs ((u : ℚ).num).natAbs := by
    simpa using (u : ℚ).reduced.symm
  have hden : ((((u : ℚ).den : ℤ) : ℚ) / ((u : ℚ).num : ℚ)).den = (u : ℚ).num.natAbs := by
    have h := Rat.den_div_eq_of_coprime hnum hcop
    have h' : (((u : ℚ).num.natAbs : ℕ) : ℤ) = (u : ℚ).num := Int.natAbs_of_nonneg hnum.le
    exact_mod_cast h.trans h'.symm
  have hnum' : ((((u : ℚ).den : ℤ) : ℚ) / ((u : ℚ).num : ℚ)).num.natAbs = (u : ℚ).den := by
    rw [Rat.num_div_eq_of_coprime hnum hcop, Int.natAbs_natCast]
  simp only [primeLatticeKernel]
  rw [hinv, hden, hnum', Complex.conj_ofReal, weilPrimeKernel_comm]

theorem isHermKernel_countertermKernel (D : ℝ) : IsHermKernel (countertermKernel D) := fun u => by
  have h1 : ((u⁻¹ : HeckeLattice) : ℚ) = 1 ↔ (u : ℚ) = 1 := by
    show (u : ℚ)⁻¹ = 1 ↔ _
    exact inv_eq_one
  simp only [countertermKernel, map_sub, isHermKernel_primeLatticeKernel u, h1]
  split_ifs <;> simp

/-- **Escape by two new primes.** -/
theorem primeLatticeKernel_escape (D : ℝ) {m n : ℕ} (x : Fin m → HeckeLattice)
    (y : Fin n → HeckeLattice) :
    ∃ t, ∀ a b, countertermKernel D ((x a)⁻¹ * (t * y b)) = 0 := by
  -- the ratios `y_b/x_a`
  set r : Fin m → Fin n → ℚ := fun a b => (y b : ℚ) / (x a : ℚ)
  set bound : ℕ := ∑ a, ∑ b, ((r a b).num.natAbs + (r a b).den)
  obtain ⟨P, hPge, hP⟩ := Nat.exists_infinite_primes (bound + 1)
  obtain ⟨Q, hQge, hQ⟩ := Nat.exists_infinite_primes (P + 1)
  have hPQ : P ≠ Q := by omega
  have hPpos : (0 : ℚ) < P := by exact_mod_cast hP.pos
  have hQpos : (0 : ℚ) < Q := by exact_mod_cast hQ.pos
  refine ⟨⟨(P : ℚ) * Q, mul_pos hPpos hQpos⟩, fun a b => ?_⟩
  set u := (x a)⁻¹ * (⟨(P : ℚ) * Q, mul_pos hPpos hQpos⟩ * y b)
  have hu : (u : ℚ) = ((r a b).num * (P * Q : ℕ) : ℤ) / ((r a b).den : ℤ) := by
    have hx : (x a : ℚ) ≠ 0 := (x a).2.ne'
    have hd : ((r a b).den : ℚ) ≠ 0 := by exact_mod_cast (r a b).den_ne_zero
    show (x a : ℚ)⁻¹ * ((P : ℚ) * Q * (y b : ℚ)) = _
    push_cast
    rw [← Rat.mul_den_eq_num (r a b)]
    simp only [r]
    field_simp
  have hbig : (r a b).num.natAbs + (r a b).den ≤ bound :=
    (Finset.single_le_sum (f := fun b => (r a b).num.natAbs + (r a b).den)
      (fun _ _ => Nat.zero_le _) (mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, ((r a b).num.natAbs + (r a b).den))
        (fun _ _ => Nat.zero_le _) (mem_univ a))
  have hrpos : 0 < r a b := div_pos (y b).2 (x a).2
  have hnum0 : 0 < (r a b).num := Rat.num_pos.mpr hrpos
  -- the new primes are coprime to the denominator
  have hcopP : Nat.Coprime P (r a b).den :=
    (hP.coprime_iff_not_dvd).mpr fun h => by have := Nat.le_of_dvd (r a b).den_pos h; omega
  have hcopQ : Nat.Coprime Q (r a b).den :=
    (hQ.coprime_iff_not_dvd).mpr fun h => by have := Nat.le_of_dvd (r a b).den_pos h; omega
  have hcop : Nat.Coprime ((r a b).num * (P * Q : ℕ) : ℤ).natAbs ((r a b).den : ℤ).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.Coprime.mul_left (r a b).reduced (Nat.Coprime.mul_left hcopP hcopQ)
  have hden := Rat.den_div_eq_of_coprime (by exact_mod_cast (r a b).den_pos) hcop
  have hnum := Rat.num_div_eq_of_coprime (by exact_mod_cast (r a b).den_pos) hcop
  rw [← hu] at hden hnum
  -- the numerator carries both new primes
  set N := (r a b).num.natAbs * (P * Q)
  have hNnum : (u : ℚ).num.natAbs = N := by rw [hnum, Int.natAbs_mul, Int.natAbs_natCast]
  have hN1 : N ≠ 1 := by
    intro h
    have : P ∣ N := Dvd.dvd.mul_left (Dvd.intro Q rfl) _
    rw [h] at this
    exact hP.one_lt.ne' (Nat.dvd_one.mp this)
  have hΛ : Λ N = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    rintro ⟨p, k, hp, hk, hpk⟩
    have hPd : P ∣ p ^ k := hpk ▸ Dvd.dvd.mul_left (Dvd.intro Q rfl) _
    have hQd : Q ∣ p ^ k := hpk ▸ Dvd.dvd.mul_left (Dvd.intro_left P rfl) _
    have h1 := (Nat.prime_dvd_prime_iff_eq hP hp.nat_prime).mp (hP.dvd_of_dvd_pow hPd)
    have h2 := (Nat.prime_dvd_prime_iff_eq hQ hp.nat_prime).mp (hQ.dvd_of_dvd_pow hQd)
    exact hPQ (h1.trans h2.symm)
  have hu1 : (u : ℚ) ≠ 1 := by
    intro h
    rw [h, Rat.num_one] at hNnum
    exact hN1 hNnum.symm
  simp only [countertermKernel, if_neg hu1, primeLatticeKernel, zero_sub, neg_eq_zero,
    Complex.ofReal_eq_zero]
  rw [hNnum]
  unfold weilPrimeKernel
  have hdN : ∀ d : ℕ, d ∣ N → d ≠ N → Nat.Coprime d N → d = 1 := fun d hd _ hc =>
    Nat.Coprime.eq_one_of_dvd hc hd
  split_ifs with h1 h2
  · -- denominator divides numerator: the denominator is one and `N/1 = N`
    have hd1 : (u : ℚ).den = 1 := by
      have hc : Nat.Coprime (u : ℚ).den N := by rw [← hNnum]; exact (u : ℚ).reduced.symm
      exact Nat.Coprime.eq_one_of_dvd hc h1.1
    rw [hd1, Nat.div_one, hΛ, zero_div]
  · -- numerator divides denominator: the numerator would be one
    have hc : Nat.Coprime N (u : ℚ).den := by rw [← hNnum]; exact (u : ℚ).reduced
    exact absurd (Nat.Coprime.eq_one_of_dvd hc h2.1) hN1
  · rfl

/-- The Gram matrix of the counterterm kernel on the atoms `1, …, N`. -/
theorem gram_countertermKernel (D : ℝ) (N : ℕ) (i j : Fin N) :
    gram (countertermKernel D) (fun k => (⟨((k : ℕ) + 1 : ℕ), by positivity⟩ : HeckeLattice)) i j =
      ((if i = j then D else 0) - weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1) : ℝ) := by
  have hval : (((⟨((i : ℕ) + 1 : ℕ), by positivity⟩ : HeckeLattice)⁻¹ *
      ⟨((j : ℕ) + 1 : ℕ), by positivity⟩ : HeckeLattice) : ℚ) =
      (((j : ℕ) + 1 : ℕ) : ℚ) / (((i : ℕ) + 1 : ℕ) : ℚ) := by
    show (((i : ℕ) + 1 : ℕ) : ℚ)⁻¹ * (((j : ℕ) + 1 : ℕ) : ℚ) = _
    ring
  simp only [gram, countertermKernel, primeLatticeKernel, hval]
  rw [weilPrimeKernel_div _ _ (Nat.succ_pos _)]
  have hone : (((j : ℕ) + 1 : ℕ) : ℚ) / (((i : ℕ) + 1 : ℕ) : ℚ) = 1 ↔ i = j := by
    rw [div_eq_one_iff_eq (by positivity)]
    constructor
    · intro h; exact Fin.ext (by exact_mod_cast (Nat.succ_injective (by exact_mod_cast h)).symm)
    · rintro rfl; rfl
  by_cases hij : i = j
  · rw [if_pos (hone.mpr hij), if_pos hij]; push_cast; ring
  · rw [if_neg (fun h => hij (hone.mp h)), if_neg hij]; push_cast; ring

/-- **No fixed counterterm makes the prime kernel Pontryagin.** For every real `D`, the kernel
`D·δ₁ − P` on the Hecke lattice has infinitely many negative squares. -/
theorem negIndex_counterterm_sub_primeLatticeKernel (D : ℝ) :
    negIndex (countertermKernel D) = ⊤ := by
  rcases negIndex_eq_zero_or_top_of_escape (isHermKernel_countertermKernel D)
    (fun _ _ x y => primeLatticeKernel_escape D x y) with h0 | htop
  · exfalso
    -- the truncated pole vector has energy above any fixed counterterm
    obtain ⟨M₀, hM₀⟩ := eventually_atomicWeilForm_truncPole_ge (η := 1) one_pos
    obtain ⟨N, hN, hN1, hlog⟩ : ∃ N, M₀ ≤ N ∧ 1 ≤ N ∧ D < Real.log N - γ - 1 := by
      obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
        ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (D + γ + 1))
      refine ⟨max N₁ (max M₀ 1), le_trans (le_max_left _ _) (le_max_right _ _),
        le_trans (le_max_right _ _) (le_max_right _ _), ?_⟩
      have := hN₁ (max N₁ (max M₀ 1)) (le_max_left _ _)
      simp only [Function.comp_apply] at this
      linarith
    have hP := hM₀ N hN
    set x : Fin N → HeckeLattice := fun k => ⟨((k : ℕ) + 1 : ℕ), by positivity⟩
    set c : Fin N → ℂ := fun k => (truncPole N ((k : ℕ) + 1) : ℂ)
    have hq := (negIndex_eq_zero_iff.mp h0) N x c
    set t : ℕ → ℝ := truncPole N
    have hK : ∀ i j : Fin N, countertermKernel D ((x i)⁻¹ * x j) =
        ((if i = j then D else 0) - weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1) : ℝ) :=
      gram_countertermKernel D N
    -- the form is `D·Σ t² − P_N(t)`
    have hform : hermQuad (gram (countertermKernel D) x) c =
        D * ∑ i : Fin N, t ((i : ℕ) + 1) ^ 2 - ∑ i : Fin N, ∑ j : Fin N,
          t ((i : ℕ) + 1) * t ((j : ℕ) + 1) * weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1) := by
      rw [hermQuad_gram]
      simp_rw [hK]
      have e : ∀ i j : Fin N, conj (c i) * (((if i = j then D else 0) -
          weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1) : ℝ) : ℂ) * c j =
          ((t ((i : ℕ) + 1) * ((if i = j then D else 0) -
            weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1)) * t ((j : ℕ) + 1) : ℝ) : ℂ) := by
        intro i j
        simp only [c, Complex.conj_ofReal]
        push_cast
        ring
      simp_rw [e]
      simp only [← Complex.ofReal_sum, Complex.ofReal_re]
      have e2 : ∀ i j : Fin N, t ((i : ℕ) + 1) * ((if i = j then D else 0) -
          weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1)) * t ((j : ℕ) + 1) =
          (if i = j then D * t ((i : ℕ) + 1) ^ 2 else 0) -
            t ((i : ℕ) + 1) * t ((j : ℕ) + 1) * weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1) := by
        intro i j
        split_ifs with h
        · subst h; ring
        · ring
      simp_rw [e2, Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (mem_univ _), Finset.mul_sum]
    -- reindex the atoms `1, …, N`
    have hre : ∀ f : ℕ → ℝ, ∑ i : Fin N, f ((i : ℕ) + 1) = ∑ n ∈ Icc 1 N, f n := fun f => by
      rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) N, Finset.range_eq_Ico,
        Finset.sum_Ico_add' f 0 N 1, zero_add, Finset.Ico_add_one_right_eq_Icc]
    have hmass : ∑ i : Fin N, t ((i : ℕ) + 1) ^ 2 = ∑ n ∈ Icc 1 N, t n ^ 2 :=
      hre fun n => t n ^ 2
    have hP' : ∑ i : Fin N, ∑ j : Fin N,
        t ((i : ℕ) + 1) * t ((j : ℕ) + 1) * weilPrimeKernel ((i : ℕ) + 1) ((j : ℕ) + 1) =
        atomicWeilForm N t := by
      rw [atomicWeilForm, ← hre fun m => ∑ n ∈ Icc 1 N, t m * t n * weilPrimeKernel m n]
      exact sum_congr rfl fun i _ => hre fun n => t ((i : ℕ) + 1) * t n *
        weilPrimeKernel ((i : ℕ) + 1) n
    -- the mass is positive: the first atom carries the pole value `1`
    have hpos : 0 < ∑ n ∈ Icc 1 N, t n ^ 2 := by
      have h1 : t 1 = 1 := by
        simp [t, RenormalizedArithmeticPotentialTheory.truncPole, hN1,
          RenormalizedArithmeticPotentialTheory.poleVector]
      have := Finset.single_le_sum (f := fun n => t n ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩)
      simp only [h1, one_pow] at this
      linarith
    rw [hform, hmass, hP'] at hq
    nlinarith
  · exact htop

end GaloisForLFunctions.AdelicKreinGeometry
