import GaloisForLFunctions.HTGeometry.ScheffeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

#check NormedSpace
#synth NormedSpace ℝ ℝ
#check Real.sqrt

theorem tmpCompileTest
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] : True := trivial

end
