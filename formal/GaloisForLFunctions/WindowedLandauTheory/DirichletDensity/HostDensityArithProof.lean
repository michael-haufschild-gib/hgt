import GaloisForLFunctions.WindowedLandauTheory.DirichletDensity.QuadDiscr
import GaloisForLFunctions.WindowedLandauTheory.DirichletDensity.MQDiscr
import GaloisForLFunctions.WindowedLandauTheory.DirichletDensity.APLogDensity
import GaloisForLFunctions.WindowedLandauTheory.DirichletDensity.LogToDir
import GaloisForLFunctions.WindowedLandauTheory.DirichletDensity.HostDensityArith
import GaloisForLFunctions.WindowedLandauTheory.DirichletDensity.HostDensity

namespace WindowedLandauTheory.HF.Final

theorem quadDiscr : WindowedLandauTheory.HF.QuadDiscr := WindowedLandauTheory.HF.quadDiscr
theorem mqDiscr : WindowedLandauTheory.HF.MQDiscr := WindowedLandauTheory.HF.mqDiscr_of quadDiscr
theorem hostDiscr : WindowedLandauTheory.HF.HostDiscr := WindowedLandauTheory.HF.hostDiscr_of mqDiscr
theorem apLogDensity : WindowedLandauTheory.HF.APLogDensity := WindowedLandauTheory.HF.apLogDensity
theorem logToDir : WindowedLandauTheory.HF.LogToDir := WindowedLandauTheory.HF.logToDir
theorem hostDensityArith : WindowedLandauTheory.HF.HostDensityArith := WindowedLandauTheory.HF.hostDensityArith_of apLogDensity logToDir
theorem hostDensity : WindowedLandauTheory.HF.HostDensity := WindowedLandauTheory.HF.hostDensity_of hostDensityArith

end WindowedLandauTheory.HF.Final
