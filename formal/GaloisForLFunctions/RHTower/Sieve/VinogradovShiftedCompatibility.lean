import GaloisForLFunctions.RHTower.Sieve.VinogradovShiftedLinnikPartner
import GaloisForLFunctions.RHTower.Sieve.VinogradovResidueTailCorrelation

/-!
# Solutions with residue-class tails force shifted nested compatibility

Let `x, y` be leading `k`-blocks with entries distinct modulo the prime `p`, and `u, v` tails whose
entries are all `≡ a (mod p)`. If `x ++ u` and `y ++ v` have equal power sums of orders `1..k`
modulo a large `q`, they have equal integer power sums. Translating every entry by `-a` keeps the
power sums equal, and each translated tail entry is a multiple of `p`, so its `j`-th power vanishes
modulo `p^j`. Hence the translated blocks `x - a` and `y - a` have equal `j`-th power sums modulo
`p^j` for `j = 1..k`.

## Main results

- `vinogradovShiftedNestedCompatible_of_residueTail_solution`: under `p` prime, `N < p^k`, `N ≠ 0`
  and `2 (k + b) N^k < q`, such a solution makes `x, y` shifted nested-compatible at `a`.

## Hypotheses

Unconditional. It assumes `p` prime, `N < p^k`, `N ≠ 0` and `2 (k + b) N^k < q`, together with the
solution equation itself.
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- Assuming `p` prime, `N < p^k`, `N ≠ 0` and `2 (k + b) N^k < q`: if `x ++ u` and `y ++ v` have equal
power sums of orders `1..k` modulo `q` and all tail entries are `≡ a (mod p)`, then the shifted blocks
`x - a`, `y - a` have equal `j`-th power sums modulo `p^j` for `j = 1..k`. -/
theorem vinogradovShiftedNestedCompatible_of_residueTail_solution
    {q N p k b : ℕ} [NeZero q] [NeZero p]
    (hp : p.Prime) (hNp : N < p ^ k) (hN : N ≠ 0)
    (hq : 2 * (k + b) * N ^ k < q)
    (a : ZMod p) (x y : VinogradovInjectiveBlock N p k)
    (u v : Fin b → VinogradovResidueClass N p a)
    (hsolution :
      vinogradovPowerSignatureMod q k
          (Fin.append x.1 (fun i => (u i).1)) =
        vinogradovPowerSignatureMod q k
          (Fin.append y.1 (fun i => (v i).1))) :
    vinogradovShiftedNestedCompatible hp hNp a x y := by
  have hpowerNat :=
    (vinogradovPowerSignatureMod_eq_iff_of_large hN hq
      (Fin.append x.1 (fun i => (u i).1))
      (Fin.append y.1 (fun i => (v i).1))).mp hsolution
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k (NeZero.ne p)⟩
  let X : Fin (k + b) → ZMod (p ^ k) :=
    fun i => ((Fin.append x.1 (fun i => (u i).1) i).val : ZMod (p ^ k))
  let Y : Fin (k + b) → ZMod (p ^ k) :=
    fun i => ((Fin.append y.1 (fun i => (v i).1) i).val : ZMod (p ^ k))
  have hpower : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      ∑ i : Fin (k + b), X i ^ j = ∑ i : Fin (k + b), Y i ^ j := by
    intro j hjpos hjk
    simpa [X, Y, Nat.cast_sum, Nat.cast_pow] using
      congrArg (fun z : ℕ => (z : ZMod (p ^ k))) (hpowerNat j hjpos hjk)
  have hshift := sum_translate_pow_eq_of_powerSums_eq
    (b := k + b) (k := k) (-(a.val : ZMod (p ^ k))) X Y hpower
  intro j
  have hjpos : 1 ≤ j.val + 1 := by omega
  have hjk : j.val + 1 ≤ k := by omega
  have hj := hshift (j.val + 1) hjpos hjk
  have hu (i : Fin b) :
      ((u i).1.val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k)) =
        (p : ZMod (p ^ k)) *
          (vinogradovResidueQuotient (u i) : ZMod (p ^ k)) := by
    rw [sub_eq_iff_eq_add]
    rw [← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg (fun z : ℕ => (z : ZMod (p ^ k)))
      (vinogradovResidue_decomposition (u i))
  have hv (i : Fin b) :
      ((v i).1.val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k)) =
        (p : ZMod (p ^ k)) *
          (vinogradovResidueQuotient (v i) : ZMod (p ^ k)) := by
    rw [sub_eq_iff_eq_add]
    rw [← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg (fun z : ℕ => (z : ZMod (p ^ k)))
      (vinogradovResidue_decomposition (v i))
  have hsplit :
      vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j +
          ∑ i : Fin b,
            (((u i).1.val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k))) ^
              (j.val + 1) =
        vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a y) j +
          ∑ i : Fin b,
            (((v i).1.val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k))) ^
              (j.val + 1) := by
    simpa [X, Y, sub_eq_add_neg, vinogradovFullPowerSignature,
      vinogradovShiftedBlock, Fin.sum_univ_add] using hj
  let d : ℕ := p ^ (j.val + 1)
  have hdvd : d ∣ p ^ k := pow_dvd_pow p hjk
  let castj : ZMod (p ^ k) →+* ZMod d := ZMod.castHom hdvd (ZMod d)
  have htailU : castj (∑ i : Fin b,
      (((u i).1.val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k))) ^
        (j.val + 1)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [hu, mul_pow, map_mul]
    change castj ((p : ZMod (p ^ k)) ^ (j.val + 1)) * _ = 0
    have hpzero : castj ((p : ZMod (p ^ k)) ^ (j.val + 1)) = 0 := by
      rw [map_pow]
      rw [map_natCast]
      rw [← Nat.cast_pow]
      simp [d]
    rw [hpzero, zero_mul]
  have htailV : castj (∑ i : Fin b,
      (((v i).1.val : ZMod (p ^ k)) - (a.val : ZMod (p ^ k))) ^
        (j.val + 1)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [hv, mul_pow, map_mul]
    change castj ((p : ZMod (p ^ k)) ^ (j.val + 1)) * _ = 0
    have hpzero : castj ((p : ZMod (p ^ k)) ^ (j.val + 1)) = 0 := by
      rw [map_pow]
      rw [map_natCast]
      rw [← Nat.cast_pow]
      simp [d]
    rw [hpzero, zero_mul]
  have hcast := congrArg castj hsplit
  simp only [map_add, htailU, htailV, add_zero] at hcast
  have hnatcast :
      ((vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j).val :
          ZMod d) =
        ((vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a y) j).val :
          ZMod d) := by
    change ZMod.cast
        (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j) =
      ZMod.cast
        (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a y) j) at hcast
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val] at hcast
    exact hcast
  exact (ZMod.natCast_eq_natCast_iff'
    (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a x) j).val
    (vinogradovFullPowerSignature (vinogradovShiftedBlock hp hNp a y) j).val d).mp hnatcast

end

end RHTower.Sieve

