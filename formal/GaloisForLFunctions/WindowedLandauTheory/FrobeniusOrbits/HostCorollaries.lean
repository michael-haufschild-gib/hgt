import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.CoprimeTwoPow
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.Galois
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ConjReal
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.RealCyclotomicSubfield
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.FrobMulInertia
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.SplitK
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.MuCardLeTwo
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.Inertia
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.Decomp
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.CardTrivialFirstComponent
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.OrderOfSignGroupDvdTwo
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.CardExtendedGaloisGroup
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.Orbits
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.DiscriminantRealSubfield
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.DiscrB
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.Principal
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ThickOrbit
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ThickFrames
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ExistsOpenNormalOrderOf
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.OrdUnimod
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.NcardEqTwoIff
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.OrbitSg
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.ThickExists
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.EqZeroOfNegEq
import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.RealSubfieldLeCompositum

namespace WindowedLandauTheory.FrobeniusOrbits.Final

open WindowedLandauTheory.FrobeniusOrbits

theorem conj : HostConj := hostConj_of hostGalois hostGalSpec
theorem real : HostReal := hostReal_of hostGalois hostGalSpec conj
theorem f1 : TwoPowerCyclotomicLayerRealSubfieldCharacterization := real_subfield_of_galois_spec hostGalSpec
theorem cmType : HostCMType := hostCMType_of hostGalois hostGalSpec
theorem frob : HostFrob := hostFrob_of hostGalois hostGalSpec
theorem splitK : HostSplitK := hostSplitK_of (hostFrob_of hostGalois hostGalSpec)
theorem efgTwo : HostEFGTwo := hostEFGTwo_of hostInertia hostDecomp
theorem ramified : HostRamified := hostRamified_of hostInertia

theorem host_field :
    HostExample ∧ HostGroup ∧ HostOrders ∧ HostRecip ∧ HostFixed ∧ HostGalois ∧ HostGalSpec ∧
    HostConj ∧ HostReal ∧ TwoPowerCyclotomicLayerRealSubfieldCharacterization ∧ HostMu ∧ HostFrob ∧ HostInertia ∧ HostUnramEF ∧
    HostDecomp ∧ HostDecompConj ∧ HostEFGTwo ∧ HostSplitK ∧ HostCMType :=
  ⟨hostExample, hostGroup, hostOrders, hostRecip, hostFixed, hostGalois, hostGalSpec, conj, real, f1, hostMu,
    frob, hostInertia, hostUnramEF, hostDecomp, hostDecompConj, efgTwo, splitK, cmType⟩

theorem host_places :
    HostThickOrbit ∧ HostThickExists ∧ HostTops ∧ HostProG ∧ HostStab ∧ HostOrdinary ∧ HostUnimodular ∧
    HostConductor ∧ HostEta ∧ HostOrbitCountSg :=
  ⟨hostThickOrbit, hostThickExists, hostTops, hostProG, hostStab, hostOrdinary, hostUnimodular,
    hostConductor, hostEta, hostOrbitCountSg⟩

end WindowedLandauTheory.FrobeniusOrbits.Final
