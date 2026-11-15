import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueFloorSum
import Mathlib.Data.Nat.ModEq

/-!
# Increasing residues of regular differential characters

The degree cutoff for an inverse radical character forces its cyclic
character weight to increase under multiplication by the branch degree.
This is the arithmetic input for descent of character weights under
Cartier's operator.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- Regular differential character weights increase under multiplication by the branch degree. -/
theorem reducedResidue_regular_character_rise (N m R : ℕ) (hN : 0 < N) (hm : 0 < m)
    (hcop : Nat.Coprime (1 + m * R) N) (i : Fin N) (k : ℕ)
    (hk : k < (i.val + m * (i.val * R % N)) / N) :
    let j := N * (k + 1) - i.val
    0 < j ∧ j < N * m ∧ j < ((1 + m * R) * j) % (N * m) := by
  let j := N * (k + 1) - i.val
  let M := N * m
  let t := m * (i.val * R % N)
  have hcut := (reducedResidue_cutoff_iff N m R hN hcop i k).mpr hk
  have hNk : N ≤ N * (k + 1) := by
    have h := Nat.mul_le_mul_left N (show 1 ≤ k + 1 by omega)
    simpa only [mul_one] using h
  have hi : i.val < N * (k + 1) := lt_of_lt_of_le i.isLt hNk
  have hjadd : j + i.val = N * (k + 1) := Nat.sub_add_cancel hi.le
  have hj : 0 < j := Nat.sub_pos_of_lt hi
  have hjt : j < t := by dsimp only [t]; omega
  have htM : t < M := by
    have h := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt (i.val * R) hN) hm
    simpa only [Nat.mul_comm m N] using h
  have hjM : j < M := hjt.trans htM
  have hM : 0 < M := Nat.mul_pos hN hm
  -- Euclidean division identifies the new residue with `M + j - t`.
  have hdecomp :
      (1 + m * R) * j + t + M * (i.val * R / N) =
        j + M * (R * (k + 1)) := by
    have hdiv := Nat.div_add_mod (i.val * R) N
    calc
      (1 + m * R) * j + t + M * (i.val * R / N) =
          j + m * R * j + m * (N * (i.val * R / N) + i.val * R % N) := by
            dsimp only [t, M]; ring
      _ = j + m * R * (j + i.val) := by rw [hdiv]; ring
      _ = j + M * (R * (k + 1)) := by rw [hjadd]; dsimp only [M]; ring
  have hres : ((1 + m * R) * j + t) % M = j := by
    have h := congrArg (fun x : ℕ => x % M) hdecomp
    simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjM] using h
  let u := ((1 + m * R) * j) % M
  let v := M + j - t
  have hu : Nat.ModEq M u ((1 + m * R) * j) := by
    exact Nat.mod_mod _ M
  have hvadd : v + t = M + j := Nat.sub_add_cancel (by omega)
  have hres' : Nat.ModEq M ((1 + m * R) * j + t) j := by
    change ((1 + m * R) * j + t) % M = j % M
    rw [hres, Nat.mod_eq_of_lt hjM]
  have hleft : Nat.ModEq M (u + t) j := (hu.add_right t).trans hres'
  have hright : Nat.ModEq M (v + t) j := by
    rw [hvadd]
    change (M + j) % M = j % M
    rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
  have huv : Nat.ModEq M u v := (hleft.trans hright.symm).add_right_cancel' t
  have huM : u < M := Nat.mod_lt _ hM
  have hvM : v < M := by dsimp only [v]; omega
  have huv' : u = v := huv.eq_of_lt_of_lt huM hvM
  change 0 < j ∧ j < M ∧ j < u
  refine ⟨hj, hjM, ?_⟩
  rw [huv']
  dsimp only [v]
  omega

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
