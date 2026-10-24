# Arithmetic Orientation Theory

Arithmetic Orientation Theory studies **source information that survives a
change of representation**: signs lost by an amplitude reading, frustration
preserved by switching, and arithmetic constraints retained under convolution
or passage to a receiver. Its aim is to turn those distinctions into usable
invariants and quantitative source estimates.

“Orientation” is not an extra positivity assumption. It names a specified
flip, switching class or source distinction that a proposed argument must
retain. A faithful reading can distinguish the relevant data; proving that
the actual source satisfies a useful bound is a further task.

## Objects and language

For a symmetric finite coupling $c$, **switching** sends
$c_{ij}$ to $s_is_jc_{ij}$ with $s_i=\pm1$. The **frustration index** is the
least number of positive overlaps left after switching; the **frustration
mass** weights them by $|c_{ij}|$. Both belong to the switching class.
The associated nonnegative signed Dirichlet form is

$$
D_c(x)=\sum_{i\ne j}|c_{ij}|
       (x_i+\operatorname{sgn}(c_{ij})x_j)^2.
$$

For source data, an **orientation** is an involutive flip $\kappa$.
A reading is **blind** if $r(\kappa d)=r(d)$ and **faithful** if it separates
every nontrivial flip pair. The even flip on four-free damped weights is a
concrete arithmetic example, not an abstract choice of an adverse companion.

A **section** of a finite observation matrix is a vector in its kernel;
$h^0$ is the kernel dimension. Frame bounds and Frobenius mass connect section
counts to the size and spacing of the observations.

The **critical Wiener algebra** consists of convolution kernels with
$\sum_n|k(n)|n^{-1/2}<\infty$. Its norm is matched to the pronic dilation cost.
A source's **repairing ideal** records kernels whose convolution admits that
source. Its common-zero **hull** and local vanishing orders describe different
parts of the obstruction.

## Foundational mechanisms

**Frustration and ground energy.** Switching preserves the Dirichlet form.
Balance is equivalent to zero frustration index; on a connected pattern it is
also equivalent to zero ground energy. Testing sign vectors bounds the ground
energy above by frustration mass. Thus locating or counting frustrating edges
does not by itself give a lower floor for the Weil form. See
[FrustrationIndexControlsTheGroundEnergy](FrustrationIndexControlsTheGroundEnergy.lean).

**An arithmetic reading of the flip.** Complete-period amplitudes and specified
translated moments can miss the even flip. The first pronic moment detects it
through an exact contribution at the prime $2$. Prime-tower product terms also
collapse to single squares, locating the frustrating prime-sum interactions.
These laws identify signed information that a subsequent estimate can use.

**Repairs with a precision cost.** In the lattice models, a sub-Nyquist sign
reading is constant throughout the admissible depth range. Crossing the
aperture threshold, measuring magnitudes or adjoining mass data gives explicit
repairs. For example, a second-band deficit budget of order $\beta^2L^3$
suffices for depth at most $\beta$. The escape theorem excludes factorization
through the blind reading; it is not an exhaustive classification of arbitrary
maps. See [TheTrichotomyOfReadings](TheTrichotomyOfReadings.lean).

**Convolution and repairing ideals.** Critical Wiener kernels act at a paid
receiver cost, and unit kernels preserve the corresponding repair class.
Finite Euler modifications, hulls and pole jets can then be studied in one
algebra. Equal hulls need not mean equal ideals: local orders matter. Turning
this algebra into a source bound requires control of the actual repairing
object, not only identification of its spectrum.

**Sections and the width dictionary.** Nyquist/frame estimates constrain how
many sections finite sampling can leave. The receiver dictionary relates
damping, growth, aperture and geometric formulations of zero width. Its
threshold object for Möbius damping packages admission at every
$\varepsilon>\sigma$; including the threshold in that categorical object does
not prove admission at $\varepsilon=\sigma$.

**Concrete calibrations.** Explicit spline sources, finite aperture chains and
the actual half-damped Möbius source instantiate the dictionaries with source
premises discharged. They make the interfaces usable; finite certificates do
not supply a cofinal gain. See
[ConcreteSourceDictionaries](ConcreteSourceDictionaries.lean).

## Research questions

- Which weighted frustration estimate transfers to the complete continuum
  Weil form with its poles and approximation errors retained?
- Can a faithful reading of the actual source be measured at the precision
  demanded by its depth or width law?
- Which repairing ideals arise from arithmetic sources, and how do hulls,
  local orders and source operations determine them?
- What source-defined section count or energy is stronger than rank–nullity
  and is independent of the desired defect sign?
- Can the signed new-prime term in the aperture shell law be bounded
  arithmetically, rather than renamed as a transport condition?

The tests for a proposed answer are concrete: specify the reading and source
class, retain its quantitative cost under limits, and explain which impure
models it excludes. A new name for zero width, a finite sign count or a source
identification theorem does not supply the missing estimate.

## Place in the wider research

[Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md)
supplies the reading calculus.
[Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md)
supplies balance and local-payment laws.
[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md)
supplies sections, effectivity and the scaling surface.
[Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md)
then studies orientation of correspondences and their orbits; this programme
concentrates on source readings and algebraic operations.

Choose the invariant and its quantitative receiver before choosing a reading.
The [programme umbrella](../ArithmeticOrientationTheory.lean) maps the
frustration, flip, section and Wiener-algebra tools.
