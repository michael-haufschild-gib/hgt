import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.MQGalois
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.MQKummer
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.MQFrob
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.KroneckerMeaning
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.TypesA
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.TypesB
import Mathlib
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.HostFrob
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.HostConj
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.HostInertia
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.HostMu
import GaloisForLFunctions.WindowedLandauTheory.CMTypeGalois.CMTypeFrobenius.HostEmb

open NumberField Ideal

namespace WindowedLandauTheory.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois
theorem mqFrob : MQFrob := mqFrob_of mqGalois
theorem hostGalois : HostGalois := hostGalois_of mqGalois mqKummer
theorem hostFrob : HostFrob := hostFrob_of mqFrob hostGalois kroneckerMeaning
theorem hostConj : HostConj := hostConj_of hostGalois mqKummer
theorem hostInertia : HostInertia := hostInertia_of hostGalois mqGalois
theorem hostMu : HostMu := hostMu_of mqKummer hostGalois
theorem hostEmb : HostEmb := hostEmb_of hostConj hostGalois

end WindowedLandauTheory.Q3
