import GaloisForLFunctions.ArithmeticKreinLangerTheory.CyclicSubgroupsDecideTheKreinLangerClass
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TowerFaithfulSpectraAreDecidedByAlmostEveryTower
import GaloisForLFunctions.ArithmeticKreinLangerTheory.LocalConstituentsMeetOnlyAtTheIdentity
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheTwistTowerCompletesTheUpperCount
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheIndexIsContinuousOffTheDiscriminant
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheParityFormOfTheGlobalLaw
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheIndexIsTheNumberOfExceptionalWaves
import GaloisForLFunctions.ArithmeticKreinLangerTheory.CompressionsAreReceivers
import GaloisForLFunctions.ArithmeticKreinLangerTheory.FineTowersDecideEveryOrbitKernel
import GaloisForLFunctions.ArithmeticKreinLangerTheory.LocalityIsTwinBlind
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheCollisionMassIsTheWaveNumber
import GaloisForLFunctions.ArithmeticKreinLangerTheory.IsolatedDeepZerosAreSeenByAlmostEveryPrime

/-!
# Arithmetic Krein–Langer theory

Umbrella for the local-to-global theory of Krein–Langer kernels on groups with a family of towers:

* **Locality.** The cyclic Hasse principle on every group, separation without torsion aliasing, the
  failure of coordinate towers on `ℤ²` and of cyclic subgroups outside the class; tower-faithful
  spectra, logarithmic spectra and the prime towers of `ℚ_{>0}`; fine towers deciding every orbit
  kernel through the archimedean place; isolated deep zeros seen by almost every prime tower;
  locality is twin-blind.
* **Local constituents and ceilings.** The Poisson law of the Euler factor, the zero-or-infinity law
  for axis-supported kernels, the Riemann–Roch ceiling, and the index as the number of exceptional
  waves of a count.
* **Producers and parity.** The quadratic twist and the twist tower over `𝔽_q`; the parity form of
  the global law over `ℤ`; compressions as receivers.
* **Completion.** Continuity of the index off the discriminant and its three degenerations; the
  heat-collision mass as twice the wave number of the prime-side count.

The foundation is `HeckeKreinToeplitz`. See `ArithmeticKreinLangerTheory/README.md`.
-/
