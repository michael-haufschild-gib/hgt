import GaloisForLFunctions.HTGeometry.AllDepthTripleCompat
import GaloisForLFunctions.HTGeometry.AllDepthCompleteness
import GaloisForLFunctions.HTGeometry.AllDepthExactImage
import GaloisForLFunctions.HTGeometry.AllDepthMultiplicative
import GaloisForLFunctions.HTGeometry.AllDepthBottomCharge
import GaloisForLFunctions.HTGeometry.PairFaceNoncompression
import GaloisForLFunctions.HTGeometry.MultipleGammaTransverseDepthNecessity

/-!
# Higher face-residue reciprocity

Dependency-closed capstone for the all-depth face-residue package:

* depth-two triptic reciprocity and completeness;
* finite all-depth pair-face signatures and triple pushforward compatibility;
* exact additive and multiplicative DA/HT classification by all pair faces;
* exact realization of every compatible finite pair-divisor family;
* bottom-charge descent and terminal-charge noncompression;
* hypertranscendental private pair carriers and exact multiple-Gamma transverse depth.

No terminal-residue compression is introduced: `PairFaceNoncompression` proves every pair sector is
necessary, while `AllDepthExactImage` identifies the image by triple compatibility.
-/
