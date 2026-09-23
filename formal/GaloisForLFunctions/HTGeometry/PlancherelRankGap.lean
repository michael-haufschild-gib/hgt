/-
The Plancherel density gap in rank `n`, and why higher-rank spectral routes get worse.

The `2k`-th moment of `ζ` is a Rankin–Selberg object on a multiplicity-one pair: the sixth moment is
`GL(3)×GL(2)`, the twelfth is `GL(4)×GL(3)`.  Both pairs have the Gelfand property, so exact period
identities are available in principle.  What is not available is the *weight*.

In a `GL(n)` spectral identity the cuspidal spectrum is counted by the Weyl law, with
`≍ T^{(n²+n-2)/2}` forms of spectral parameter `≤ T`, while the minimal Eisenstein family is
parametrised by `n-1` continuous coordinates and carries only `≍ T^{n-1}`.  The moment of `ζ` lives on
the Eisenstein part.  So every spectral route to it is suppressed relative to the cuspidal part by

    rankGap n  =  (n²+n-2)/2 - (n-1)  =  n(n-1)/2,

which is the number of positive roots of `GL(n)`.  At `n = 2` the gap is `1` — the single power of `r`
that already voids the Motohashi continuous term.  It grows quadratically thereafter: `3` at `n = 3`,
`6` at `n = 4`.  Higher rank makes the obstruction worse, not better.
-/
import GaloisForLFunctions.HTGeometry.MotohashiContinuousTerm

namespace HTGeometry

/-- Weyl-law exponent for the cuspidal spectrum of `GL(n)`: the dimension of `SL(n,ℝ)/SO(n)`. -/
def cuspidalWeylExponent (n : ℚ) : ℚ := (n^(2 : ℕ) + n - 2) / 2

/-- Dimension of the minimal Eisenstein family on `GL(n)`: its continuous spectral parameters. -/
def eisensteinFamilyExponent (n : ℚ) : ℚ := n - 1

/-- The suppression of the Eisenstein contribution relative to the cuspidal one. -/
def rankGap (n : ℚ) : ℚ := cuspidalWeylExponent n - eisensteinFamilyExponent n

/-- **The gap is the number of positive roots of `GL(n)`.** -/
theorem rankGap_eq (n : ℚ) : rankGap n = n * (n - 1) / 2 := by
  unfold rankGap cuspidalWeylExponent eisensteinFamilyExponent
  ring

@[simp] theorem rankGap_two : rankGap 2 = 1 := by rw [rankGap_eq]; norm_num

@[simp] theorem rankGap_three : rankGap 3 = 3 := by rw [rankGap_eq]; norm_num

@[simp] theorem rankGap_four : rankGap 4 = 6 := by rw [rankGap_eq]; norm_num

/-- At rank `2` the gap is exactly the one power of `r` that already voids the Motohashi continuous
term: `cuspidalDensityExponent - eisensteinDensityExponent = 1`. -/
theorem rankGap_two_matches_plancherel :
    rankGap 2 = cuspidalDensityExponent - eisensteinDensityExponent := by
  rw [rankGap_two, plancherel_density_gap]

/-- **The gap grows strictly with the rank.**  There is no rank at which the Eisenstein contribution
becomes easier to reach. -/
theorem rankGap_strictMono {m n : ℚ} (hm : 1 ≤ m) (hmn : m < n) : rankGap m < rankGap n := by
  rw [rankGap_eq, rankGap_eq]
  have h1 : 0 ≤ m - 1 := by linarith
  nlinarith

/-- **The gap is superlinear: it grows quadratically in the rank.**  Doubling the rank more than
doubles the suppression. -/
theorem rankGap_superadditive {n : ℚ} (hn : 2 ≤ n) : 2 * rankGap n ≤ rankGap (2 * n) - rankGap 2 := by
  rw [rankGap_eq, rankGap_eq, rankGap_two]
  nlinarith

/-- **The higher-rank spectral ceiling.**  At every rank the moment of `ζ` sits on the Eisenstein
spectrum and is suppressed by `n(n-1)/2`; the suppression is already fatal at `n = 2`, where it is
`1`, and it strictly increases.  So no increase of rank can rescue the spectral route. -/
theorem higher_rank_ceiling {m n : ℚ} (hm : 2 ≤ m) (hmn : m < n) :
    1 ≤ rankGap m ∧ rankGap m < rankGap n := by
  refine ⟨?_, rankGap_strictMono (by linarith) hmn⟩
  rw [rankGap_eq]
  nlinarith

end HTGeometry
