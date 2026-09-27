# Prime and prime-square normal jets give a two-level line classifier — Lean certificate

- **Paper card:** `theta-prime-square-two-level-normal-jet-rigidity.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaPrimeSquareNormalJetRigidity`
  (algebraic core `PrimeSquareTwoLevelReflectedRigidity.epsilon_eq_zero_of_prime_and_square_reflected_modulus_neutral`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 9 listed theorems; no `sorry`.

`F = thetaSourceTransform` (`F(w) = XiC(i w) = L_w k`), `D_{p^j} = thetaPrimePowerDeletion p j`,
`F_{p^j} = thetaPrimePowerDeletedTransform p j`, `E_j = primePowerEulerFactor p j`.
A zero of multiplicity `m` is encoded as: `iteratedDeriv i F w₀ = 0` for `i < m` and
`iteratedDeriv m F w₀ ≠ 0`.

| Card item | Lean theorem |
|-|-|
| `D_{p^j}k` removes exactly the atoms divisible by `p^j` | `thetaPrimePowerDeletion_eq_tsum` |
| `D_{p²} = (1+A)D_p` | `thetaPrimePowerDeletion_two_eq` |
| (1) `F_{p^j}(w) = F(w)(1 - p^{-j(1/2+w)})` | `integral_cexp_mul_thetaPrimePowerDeletion`, `thetaPrimePowerDeletedTransform_eq_integral` |
| factor nonzero for `Re w > -1/2` | `primePowerEulerFactor_ne_zero` |
| (2) first nonzero deleted jet `= F^{(m)}(w₀)(1 - p^{-j(1/2+w₀)})` | `thetaPrimePowerDeleted_jet` (Leibniz: `iteratedDeriv_mul_of_lower_vanish`) |
| base jets at `w₀`, `-conj w₀`: equal moduli, same multiplicity | `iteratedDeriv_thetaSourceTransform_neg_conj`, `norm_iteratedDeriv_thetaSourceTransform_neg_conj`, `iteratedDeriv_thetaSourceTransform_neg_conj_eq_zero_iff` |
| (3) equal reflected deleted-jet moduli at `p` and `p²` ⇒ `Re w₀ = 0` | `re_eq_zero_of_prime_and_square_deleted_jets` |
| one level is insufficient | `exists_phase_one_level_neutral` |
