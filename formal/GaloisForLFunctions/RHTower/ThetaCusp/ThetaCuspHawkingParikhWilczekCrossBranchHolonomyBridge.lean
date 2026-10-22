import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent

/-!
# Literal complementary Peierls parameter / PW Borel-holonomy bridge

The complementary literal Peierls branches have an actual reflection-even
angular coefficient `parameter₊ + parameter₋`.  The PW closed recoil history
at every Borel grade is also reflection even.  This leaf proves their exact
all-grade algebraic relation, without assigning a boundary normalization or
replacing the full CTP source by a scalar model.

Proof-chain role:
`literal complementary Peierls parameter -> PW even closed-history coordinate`
`+ literal full CTP odd orientation -> source-to-PW magnitude normalization`
`-> fixed-grade PW balance -> Xi occurrence -> RH`.

The remaining PW-B source obligation is now precise: identify the normalized
reflection-odd full CTP numerator, including cap/lift-defect transport, with
the PW real partner imbalance.  No spectral-coordinate or reflection-parity
choice remains.

`[NEW] [PW-B SOURCE SPECTRAL BRIDGE] [LEAN-PROVED]`
-/

namespace RHTower

open D4BMGlobalAngularResponse D4BMModularCore D4BMQuadraticMixedSource

noncomputable section

/-- Reflection-even angular parameter of the two literal complementary
Peierls source branches. -/
def d4BMPeierlsCrossAngularParameter (q : XiZeroCopy) : ℂ :=
  parameter q true + parameter q false

/-- Exact literal-coordinate form of the complementary source parameter. -/
theorem d4BMPeierlsCrossAngularParameter_eq (q : XiZeroCopy) :
    d4BMPeierlsCrossAngularParameter q =
      8 * (q.1 : ℂ) ^ (2 : ℕ) - 8 * (q.1 : ℂ) + 6 := by
  unfold d4BMPeierlsCrossAngularParameter
  rw [D4BMModularCore.parameter_physicalRate q true,
    D4BMModularCore.parameter_physicalRate q false]
  simp only [D4BMModularCore.physicalRate, if_true, Bool.false_eq_true, if_false,
    D4BMQuadraticMixedSource.resolventParameter]
  ring

/-- Functional-equation reflection fixes the literal complementary parameter. -/
theorem d4BMPeierlsCrossAngularParameter_reflect (q : XiZeroCopy) :
    d4BMPeierlsCrossAngularParameter (xiZeroCopyReflectEquiv q) =
      d4BMPeierlsCrossAngularParameter q := by
  rw [d4BMPeierlsCrossAngularParameter_eq,
    d4BMPeierlsCrossAngularParameter_eq]
  change 8 * (1 - (q.1 : ℂ)) ^ (2 : ℕ) - 8 * (1 - (q.1 : ℂ)) + 6 = _
  ring

/-- PW closed-history recoil holonomy at one literal Xi copy and Borel grade. -/
def d4BMPeierlsCrossBorelHolonomy (q : XiZeroCopy) (k : ℕ) : ℂ :=
  schwarzschildParikhWilczekBorelRecoilHolonomy (q.1 : ℂ) k

/-- **All-grade complementary source bridge.** The PW closed recoil holonomy
is a grade-dependent quadratic polynomial of the literal complementary
Peierls angular parameter. -/
theorem d4BMPeierlsCrossBorelHolonomy_polynomial (q : XiZeroCopy) (k : ℕ) :
    64 * d4BMPeierlsCrossBorelHolonomy q k =
      d4BMPeierlsCrossAngularParameter q ^ (2 : ℕ) -
        (16 * (2 * (k : ℂ) + 1) ^ (2 : ℕ) + 12) *
          d4BMPeierlsCrossAngularParameter q +
        64 * (2 * (k : ℂ) + 1) ^ (4 : ℕ) +
          32 * (2 * (k : ℂ) + 1) ^ (2 : ℕ) + 36 := by
  rw [d4BMPeierlsCrossAngularParameter_eq]
  simp only [d4BMPeierlsCrossBorelHolonomy,
    schwarzschildParikhWilczekBorelRecoilHolonomy,
    schwarzschildParikhWilczekBorelRecoilEdge]
  ring

end

end RHTower
