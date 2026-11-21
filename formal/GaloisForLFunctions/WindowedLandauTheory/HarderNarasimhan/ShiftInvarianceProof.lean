import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.DegSupermodZProof
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.ExistsSmulMemOfFinrankEq
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.FinSup
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.SatBasic
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.RatioMax
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.DegSupermod
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.MuChar
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.HNStep
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.SlopeIneq
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.PolygonSlopeSum
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.HNSlopes
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.ShiftInvariance
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.Duality
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.HNExtreme
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.PiSumForallInsertOnly
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.Example
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.DiscreteSpanOfLinIndep
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.SizeMu
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.PlaceSplit
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.GramBlock
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.RescaleCovol
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.TwistFinrankEq
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.SlopeIneqMean
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.HtGram
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.HtImage
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.SizeIneq
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.Rerealize
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.FrameHermSharpB
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.QuotRealizeProof
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.FrameLinearAlgebraFirst
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.TheoremFSharp
import GaloisForLFunctions.WindowedLandauTheory.HarderNarasimhan.DualPl

namespace WindowedLandauTheory.HN

theorem satR : SatR := real_saturation_property
theorem finSup : FinSup := finite_supremum_slopes
theorem satBasic : SatBasic := saturation_basic_properties
theorem ratioMax : RatioMax := maximal_slope_ratio
theorem degSupermod : DegSupermod := degree_supermodular
theorem muChar : MuChar := slope_characterization
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
theorem slopeIneq : SlopeIneq := slope_inequality_general
theorem hnSum : HNSum := polygon_slope_sum
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
theorem duality : Duality := slope_duality_formula
theorem piSum : PiSum := product_slope_sum
theorem plLat : PlLat := place_lattice_structure
theorem sizeMu : SizeMu := size_maximal_slope
theorem gramBlock : GramBlock := gram_block_determinant
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
theorem htGram : HtGram := height_gram_determinant
theorem htImage : HtImage := height_image_formula
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
theorem rerealize : Rerealize := lattice_rerealization
theorem quotRealize : QuotRealize := quotient_lattice_realization
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
theorem theoremF : TheoremF := frame_theorem_log_ideal
theorem dualPl : DualPl := dual_polygon_identity

end WindowedLandauTheory.HN
