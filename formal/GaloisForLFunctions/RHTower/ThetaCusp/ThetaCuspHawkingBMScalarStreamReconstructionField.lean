import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamReconstructionJet
import GaloisForLFunctions.HTGeometry.TwistedRadialDerivative

/-!
# Sourced Kodama–Ishibashi reconstruction of the harmonic scalar stream (field level)

The jet-level reconstruction identities are applied to actual radial functions. For an undressed
master function `y` and undressed source coefficients `tTT, …, tL` (the dressed fields are
`B²·y`, `B²·tA` with `(B²)'/B² = 2s/(r(r²−1))`), the symbols of the jet identities are the iterated
twisted derivatives `twistIter s k`. Each reconstructed jet form is realised as a rational-coefficient
linear form (`…R`), shown equal to the jet-level form at the twisted jets (`…R_eq`), and its twisted
derivative is the next form of its chain (`twist_…R`). With the sourced master equation and the three
Bianchi identities of the source holding on the exterior, the seven sourced harmonic Einstein
equations hold at every exterior radius for the twisted two-jets of the reconstructed radial functions
(`sourced_equation_TT`, …). All derivative bookkeeping is done by `twist_linear`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry CoordinateMetricTwoJet GaloisForLFunctions.HTGeometry.TwistedRadial
open Filter Topology
noncomputable section

/-- The first `n` twisted derivatives of `g` are differentiable on the exterior `r > 1`. -/
def TwistSmooth (s : ℂ) (g : ℝ → ℂ) (n : ℕ) : Prop :=
  ∀ r : ℝ, 1 < r → ∀ k, k < n → DifferentiableAt ℝ (twistIter s k g) r

theorem exterior_ne (r : ℝ) (hr1 : 1 < r) : (r : ℂ) ≠ 0 ∧ (r : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
  constructor
  · exact_mod_cast (by linarith : r ≠ 0)
  · exact_mod_cast (by nlinarith : r ^ (2 : ℕ) - 1 ≠ 0)

theorem exterior_eventually {r : ℝ} (hr1 : 1 < r) : ∀ᶠ r' in 𝓝 r, 1 < r' :=
  isOpen_Ioi.mem_nhds hr1

theorem TwistSmooth.mono {s : ℂ} {g : ℝ → ℂ} {n m : ℕ} (h : TwistSmooth s g n) (hmn : m ≤ n) :
    TwistSmooth s g m :=
  fun r hr k hk => h r hr k (lt_of_lt_of_le hk hmn)

/-- Horner coefficient lists of `recF0` over `r ^ (1 : ℕ) (r² − 1) ^ (0 : ℕ)`. -/
def recF0CS (s μ : ℂ) : Fin 10 → List ℂ :=
  ![[(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (((-2 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (((6 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-10 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recF0`. -/
def recF0X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 10 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF]

/-- `recF0` as a rational-coefficient linear form in the twisted jets. -/
def recF0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF0CS s μ i) 1 0 r * recF0X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recF01` over `r ^ (2 : ℕ) (r² − 1) ^ (1 : ℕ)`. -/
def recF01CS (s μ : ℂ) : Fin 14 → List ℂ :=
  ![[(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((11 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ))), (0 : ℂ), (((7 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-13 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((27 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((21 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-9 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((28 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (((4 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-22 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((32 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((20 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-36 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((16 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((64 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-96 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((44 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((40 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-50 : ℂ)) / ((2 - μ))), (0 : ℂ), (((20 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recF01`. -/
def recF01X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 14 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF]

/-- `recF01` as a rational-coefficient linear form in the twisted jets. -/
def recF01R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF01CS s μ i) 2 1 r * recF01X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recF02` over `r ^ (3 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def recF02CS (s μ : ℂ) : Fin 18 → List ℂ :=
  ![[(((-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((36 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-54 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ) + (3 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((84 : ℂ) + (-3 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-96 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((36 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-21 : ℂ)) / ((2 - μ))), (0 : ℂ), (((45 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-39 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((24 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-108 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((144 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-60 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((56 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-160 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((168 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-60 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((30 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-60 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((50 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((12 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-72 : ℂ) + (4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((108 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-48 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((48 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-168 : ℂ) + (8 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((192 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-72 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-6 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((42 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-90 : ℂ) + (3 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((78 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-20 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((88 : ℂ) + (-12 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-116 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((48 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-124 : ℂ) + (12 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((440 : ℂ) + (-24 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-508 : ℂ) + (12 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((192 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((22 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-186 : ℂ) + (9 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((450 : ℂ) + (-9 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-430 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((144 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-74 : ℂ)) / ((2 - μ))), (0 : ℂ), (((138 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-110 : ℂ)) / ((2 - μ))), (0 : ℂ), (((32 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recF02`. -/
def recF02X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 18 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 4 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 3 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 3 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF, twistIter s 4 tTF]

/-- `recF02` as a rational-coefficient linear form in the twisted jets. -/
def recF02R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF02CS s μ i) 3 2 r * recF02X s y tTT tTR tRR tT tR tTF tL i r

theorem recF0R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF0R s μ y tTT tTR tRR tT tR tTF tL r = recF0 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF0R recF0CS recF0X recF0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recF0R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))] 1 0 r = ratCoef [(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 0 r + ratCoef [(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 0 r + ratCoef [(0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((11 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ))), (0 : ℂ), (((7 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-13 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((27 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 1 0 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((21 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-9 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-2 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((28 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 1 0 r + ratCoef [(0 : ℂ), (((-2 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((4 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-22 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((32 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((6 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-10 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((20 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-36 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((16 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 1 0 r + ratCoef [(0 : ℂ), (((6 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-10 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((64 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-96 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((44 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 0 r + ratCoef [(0 : ℂ), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((40 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-50 : ℂ)) / ((2 - μ))), (0 : ℂ), (((20 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF0R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recF0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 3) (hTR : TwistSmooth s tTR 2) (hT : TwistSmooth s tT 2) (hTF : TwistSmooth s tTF 3) :
    twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r = recF01R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF0R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recF0X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num))]
  unfold recF01R recF0CS recF01CS recF0X recF01X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recF0R_P s μ hr1 + (twist s (y) r) * twist_recF0R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recF0R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_recF0R_P3 s μ hr1 + (tTR r) * twist_recF0R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recF0R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_recF0R_qtr2 s μ hr1 + (tT r) * twist_recF0R_qt0 s μ hr1 + (twist s (tT) r) * twist_recF0R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_recF0R_qt2 s μ hr1 + (tTF r) * twist_recF0R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recF0R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recF0R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_recF0R_qT3 s μ hr1

theorem recF01R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF01R s μ y tTT tTR tRR tT tR tTF tL r = recF01 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF01R recF01CS recF01X recF01
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recF01R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))] 2 1 r = ratCoef [(((-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ) * μ) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (((1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((36 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-54 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((11 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ))), (0 : ℂ), (((7 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ) + (3 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((84 : ℂ) + (-3 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-96 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((36 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((11 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ))), (0 : ℂ), (((7 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-21 : ℂ)) / ((2 - μ))), (0 : ℂ), (((45 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-39 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_P4 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-13 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((27 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((24 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-108 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((144 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-60 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((21 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-9 : ℂ)) / ((2 - μ) * s))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-13 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((27 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((56 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-160 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((168 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-60 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((21 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-9 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((30 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-60 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((50 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-15 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qtr3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((28 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((12 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-72 : ℂ) + (4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((108 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-48 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((4 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-22 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((32 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ) * s))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((28 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-16 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((48 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-168 : ℂ) + (8 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((192 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-72 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((4 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-22 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((32 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-6 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((42 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-90 : ℂ) + (3 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((78 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qt3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((20 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-36 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((16 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-20 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((88 : ℂ) + (-12 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-116 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((48 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((64 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-96 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((44 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((20 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-36 : ℂ) + (6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((16 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-124 : ℂ) + (12 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((440 : ℂ) + (-24 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-508 : ℂ) + (12 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((192 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((40 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-50 : ℂ)) / ((2 - μ))), (0 : ℂ), (((20 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-12 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((64 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-96 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((44 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((22 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-186 : ℂ) + (9 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((450 : ℂ) + (-9 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-430 : ℂ) + (3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((144 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((40 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-50 : ℂ)) / ((2 - μ))), (0 : ℂ), (((20 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-74 : ℂ)) / ((2 - μ))), (0 : ℂ), (((138 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-110 : ℂ)) / ((2 - μ))), (0 : ℂ), (((32 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF01R_qT4 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recF01R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 4) (hTR : TwistSmooth s tTR 3) (hT : TwistSmooth s tT 3) (hTF : TwistSmooth s tTF 4) :
    twist s (recF01R s μ y tTT tTR tRR tT tR tTF tL) r = recF02R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF01R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recF01X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hy r hr1 3 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hTR r hr1 2 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hT r hr1 2 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num) | exact hTF r hr1 3 (by norm_num))]
  unfold recF02R recF01CS recF02CS recF01X recF02X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recF01R_P s μ hr1 + (twist s (y) r) * twist_recF01R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recF01R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_recF01R_P3 s μ hr1 + (twist s (twist s (twist s (twist s (y)))) r) * twist_recF01R_P4 s μ hr1 + (tTR r) * twist_recF01R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recF01R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_recF01R_qtr2 s μ hr1 + (twist s (twist s (twist s (tTR))) r) * twist_recF01R_qtr3 s μ hr1 + (tT r) * twist_recF01R_qt0 s μ hr1 + (twist s (tT) r) * twist_recF01R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_recF01R_qt2 s μ hr1 + (twist s (twist s (twist s (tT))) r) * twist_recF01R_qt3 s μ hr1 + (tTF r) * twist_recF01R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recF01R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recF01R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_recF01R_qT3 s μ hr1 + (twist s (twist s (twist s (twist s (tTF)))) r) * twist_recF01R_qT4 s μ hr1

theorem recF02R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF02R s μ y tTT tTR tRR tT tR tTF tL r = recF02 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF02R recF02CS recF02X recF02
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `recF1` over `r ^ (0 : ℕ) (r² − 1) ^ (1 : ℕ)`. -/
def recF1CS (s μ : ℂ) : Fin 6 → List ℂ :=
  ![[(((-2 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (((-2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))]]

/-- Symbol functions of `recF1`. -/
def recF1X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 0 tTR, twistIter s 0 tT, twistIter s 0 tTF, twistIter s 1 tTF]

/-- `recF1` as a rational-coefficient linear form in the twisted jets. -/
def recF1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF1CS s μ i) 0 1 r * recF1X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recF11` over `r ^ (1 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def recF11CS (s μ : ℂ) : Fin 10 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (((8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-28 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))]]

/-- Symbol functions of `recF11`. -/
def recF11X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 10 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF]

/-- `recF11` as a rational-coefficient linear form in the twisted jets. -/
def recF11R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF11CS s μ i) 1 2 r * recF11X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recF12` over `r ^ (2 : ℕ) (r² − 1) ^ (3 : ℕ)`. -/
def recF12CS (s μ : ℂ) : Fin 13 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((8 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-24 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-24 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((48 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-40 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-24 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((68 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-64 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((20 : ℂ) * s) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))]]

/-- Symbol functions of `recF12`. -/
def recF12X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 13 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 1 tT, twistIter s 2 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF]

/-- `recF12` as a rational-coefficient linear form in the twisted jets. -/
def recF12R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF12CS s μ i) 2 3 r * recF12X s y tTT tTR tRR tT tR tTF tL i r

theorem recF1R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF1R s μ y tTT tTR tRR tT tR tTF tL r = recF1 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF1R recF1CS recF1X recF1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recF1R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((-2 : ℂ) * s) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 0 1 r + ratCoef [(((-2 : ℂ) * s) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (((-2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (((8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 0 1 r + ratCoef [(0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-28 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) * s) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF1R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 0 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recF1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 2) (hTR : TwistSmooth s tTR 1) (hT : TwistSmooth s tT 1) (hTF : TwistSmooth s tTF 2) :
    twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r = recF11R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF1R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recF1X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num))]
  unfold recF11R recF1CS recF11CS recF1X recF11X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recF1R_P s μ hr1 + (twist s (y) r) * twist_recF1R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recF1R_P2 s μ hr1 + (tTR r) * twist_recF1R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recF1R_qtr1 s μ hr1 + (tT r) * twist_recF1R_qt0 s μ hr1 + (twist s (tT) r) * twist_recF1R_qt1 s μ hr1 + (tTF r) * twist_recF1R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recF1R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recF1R_qT2 s μ hr1

theorem recF11R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF11R s μ y tTT tTR tRR tT tR tTF tL r = recF11 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF11R recF11CS recF11X recF11
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recF11R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 1 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((8 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 1 2 r + ratCoef [(0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-14 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))] 1 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r = (0 : ℂ) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r + ratCoef [(0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-24 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-28 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) * s) / ((2 - μ)))] 1 2 r + ratCoef [(0 : ℂ), (((8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-24 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((48 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-40 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((16 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-28 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-24 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((68 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-64 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((20 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF11R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-8 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 1 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((-12 : ℂ) * s) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) * s) / ((2 - μ)))] 2 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recF11R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 3) (hTR : TwistSmooth s tTR 2) (hT : TwistSmooth s tT 2) (hTF : TwistSmooth s tTF 3) :
    twist s (recF11R s μ y tTT tTR tRR tT tR tTF tL) r = recF12R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF11R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recF11X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num))]
  unfold recF12R recF11CS recF12CS recF11X recF12X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recF11R_P s μ hr1 + (twist s (y) r) * twist_recF11R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recF11R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_recF11R_P3 s μ hr1 + (tTR r) * twist_recF11R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recF11R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_recF11R_qtr2 s μ hr1 + (tT r) * twist_recF11R_qt0 s μ hr1 + (twist s (tT) r) * twist_recF11R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_recF11R_qt2 s μ hr1 + (tTF r) * twist_recF11R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recF11R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recF11R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_recF11R_qT3 s μ hr1

theorem recF12R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF12R s μ y tTT tTR tRR tT tR tTF tL r = recF12 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF12R recF12CS recF12X recF12
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `recF2` over `r ^ (1 : ℕ) (r² − 1) ^ (1 : ℕ)`. -/
def recF2CS (s μ : ℂ) : Fin 10 → List ℂ :=
  ![[(((1 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (((2 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (((-2 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recF2`. -/
def recF2X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 10 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF]

/-- `recF2` as a rational-coefficient linear form in the twisted jets. -/
def recF2R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF2CS s μ i) 1 1 r * recF2X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recF21` over `r ^ (2 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def recF21CS (s μ : ℂ) : Fin 14 → List ℂ :=
  ![[(((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-3 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((10 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((8 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-22 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recF21`. -/
def recF21X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 14 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF]

/-- `recF21` as a rational-coefficient linear form in the twisted jets. -/
def recF21R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF21CS s μ i) 2 2 r * recF21X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recF22` over `r ^ (3 : ℕ) (r² − 1) ^ (3 : ℕ)`. -/
def recF22CS (s μ : ℂ) : Fin 18 → List ℂ :=
  ![[(((1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) + (4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-11 : ℂ)) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((28 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((5 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-17 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((19 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-7 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-12 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-8 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ) + (4 : ℂ) * μ) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-20 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((22 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) + (2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) + (6 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((20 : ℂ) + (4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-18 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((68 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-74 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((44 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-46 : ℂ)) / ((2 - μ))), (0 : ℂ), (((16 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recF22`. -/
def recF22X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 18 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 4 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 3 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 3 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF, twistIter s 4 tTF]

/-- `recF22` as a rational-coefficient linear form in the twisted jets. -/
def recF22R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recF22CS s μ i) 3 3 r * recF22X s y tTT tTR tRR tT tR tTF tL i r

theorem recF2R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF2R s μ y tTT tTR tRR tT tR tTF tL r = recF2 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF2R recF2CS recF2X recF2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recF2R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((1 / 2 : ℂ) * μ) / ((2 - μ)))] 1 1 r = ratCoef [(((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-3 / 2 : ℂ) * μ) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 1 r + ratCoef [(((1 / 2 : ℂ) * μ) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 1 r + ratCoef [(0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 1 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((2 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 1 1 r + ratCoef [(0 : ℂ), (((2 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((10 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-2 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 1 1 r + ratCoef [(0 : ℂ), (((-2 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((8 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((8 : ℂ)) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-22 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF2R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 1 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recF2R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 3) (hTR : TwistSmooth s tTR 2) (hT : TwistSmooth s tT 2) (hTF : TwistSmooth s tTF 3) :
    twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r = recF21R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF2R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recF2X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num))]
  unfold recF21R recF2CS recF21CS recF2X recF21X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recF2R_P s μ hr1 + (twist s (y) r) * twist_recF2R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recF2R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_recF2R_P3 s μ hr1 + (tTR r) * twist_recF2R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recF2R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_recF2R_qtr2 s μ hr1 + (tT r) * twist_recF2R_qt0 s μ hr1 + (twist s (tT) r) * twist_recF2R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_recF2R_qt2 s μ hr1 + (tTF r) * twist_recF2R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recF2R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recF2R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_recF2R_qT3 s μ hr1

theorem recF21R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF21R s μ y tTT tTR tRR tT tR tTF tL r = recF21 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF21R recF21CS recF21X recF21
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recF21R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-3 / 2 : ℂ) * μ) / ((2 - μ)))] 2 2 r = ratCoef [(((1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) * μ) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ)))] 2 2 r + ratCoef [(((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-3 / 2 : ℂ) * μ) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (((-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) + (4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((6 : ℂ) + (-3 : ℂ) * μ) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ)))] 2 2 r + ratCoef [(0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-11 : ℂ)) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_P4 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-12 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-24 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((28 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((5 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-17 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((19 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-7 : ℂ)) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qtr3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-12 : ℂ) + (-6 : ℂ) * μ) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((10 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-8 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ) + (4 : ℂ) * μ) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((10 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((6 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-20 : ℂ) + (2 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((22 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ) * s)), (0 : ℂ), (((-8 : ℂ)) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qt3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ) + (2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((12 : ℂ) + (6 : ℂ) * μ) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((8 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((20 : ℂ) + (4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) + (-4 : ℂ) * μ) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-22 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (((8 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-24 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-18 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((68 : ℂ) + (-2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-74 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((24 : ℂ)) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-22 : ℂ)) / ((2 - μ))), (0 : ℂ), (((12 : ℂ)) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-14 : ℂ)) / ((2 - μ))), (0 : ℂ), (((44 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-46 : ℂ)) / ((2 - μ))), (0 : ℂ), (((16 : ℂ)) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recF21R_qT4 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recF21R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 4) (hTR : TwistSmooth s tTR 3) (hT : TwistSmooth s tT 3) (hTF : TwistSmooth s tTF 4) :
    twist s (recF21R s μ y tTT tTR tRR tT tR tTF tL) r = recF22R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF21R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recF21X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hy r hr1 3 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hTR r hr1 2 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hT r hr1 2 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num) | exact hTF r hr1 3 (by norm_num))]
  unfold recF22R recF21CS recF22CS recF21X recF22X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recF21R_P s μ hr1 + (twist s (y) r) * twist_recF21R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recF21R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_recF21R_P3 s μ hr1 + (twist s (twist s (twist s (twist s (y)))) r) * twist_recF21R_P4 s μ hr1 + (tTR r) * twist_recF21R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recF21R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_recF21R_qtr2 s μ hr1 + (twist s (twist s (twist s (tTR))) r) * twist_recF21R_qtr3 s μ hr1 + (tT r) * twist_recF21R_qt0 s μ hr1 + (twist s (tT) r) * twist_recF21R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_recF21R_qt2 s μ hr1 + (twist s (twist s (twist s (tT))) r) * twist_recF21R_qt3 s μ hr1 + (tTF r) * twist_recF21R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recF21R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recF21R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_recF21R_qT3 s μ hr1 + (twist s (twist s (twist s (twist s (tTF)))) r) * twist_recF21R_qT4 s μ hr1

theorem recF22R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recF22R s μ y tTT tTR tRR tT tR tTF tL r = recF22 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recF22R recF22CS recF22X recF22
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `recH` over `r ^ (1 : ℕ) (r² − 1) ^ (0 : ℕ)`. -/
def recHCS (s μ : ℂ) : Fin 6 → List ℂ :=
  ![[(((-1 / 4 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (((-1 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recH`. -/
def recHX (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 0 tTR, twistIter s 0 tT, twistIter s 0 tTF, twistIter s 1 tTF]

/-- `recH` as a rational-coefficient linear form in the twisted jets. -/
def recHR (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recHCS s μ i) 1 0 r * recHX s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recH1` over `r ^ (2 : ℕ) (r² − 1) ^ (1 : ℕ)`. -/
def recH1CS (s μ : ℂ) : Fin 10 → List ℂ :=
  ![[(((-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ) + (-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recH1`. -/
def recH1X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 10 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF]

/-- `recH1` as a rational-coefficient linear form in the twisted jets. -/
def recH1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recH1CS s μ i) 2 1 r * recH1X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `recH2` over `r ^ (3 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def recH2CS (s μ : ℂ) : Fin 14 → List ℂ :=
  ![[(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ)))], [(0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (((-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) + (-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((7 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-20 : ℂ)) / ((2 - μ))), (0 : ℂ), (((10 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((13 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-17 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((7 : ℂ)) / ((2 - μ)))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))]]

/-- Symbol functions of `recH2`. -/
def recH2X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 14 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF]

/-- `recH2` as a rational-coefficient linear form in the twisted jets. -/
def recH2R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (recH2CS s μ i) 3 2 r * recH2X s y tTT tTR tRR tT tR tTF tL i r

theorem recHR_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recHR s μ y tTT tTR tRR tT tR tTF tL r = recH s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recHR recHCS recHX recH
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recHR_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((-1 / 4 : ℂ) * μ) / ((2 - μ)))] 1 0 r = ratCoef [(((-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))] 1 0 r + ratCoef [(((-1 / 4 : ℂ) * μ) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ) + (-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((-1 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 0 r + ratCoef [(0 : ℂ), (((-1 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recHR_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 1 0 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recHR (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 2) (hTR : TwistSmooth s tTR 1) (hT : TwistSmooth s tT 1) (hTF : TwistSmooth s tTF 2) :
    twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r = recH1R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recHR
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recHX, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num))]
  unfold recH1R recHCS recH1CS recHX recH1X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recHR_P s μ hr1 + (twist s (y) r) * twist_recHR_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recHR_P2 s μ hr1 + (tTR r) * twist_recHR_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recHR_qtr1 s μ hr1 + (tT r) * twist_recHR_qt0 s μ hr1 + (twist s (tT) r) * twist_recHR_qt1 s μ hr1 + (tTF r) * twist_recHR_qT0 s μ hr1 + (twist s (tTF) r) * twist_recHR_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recHR_qT2 s μ hr1

theorem recH1R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recH1R s μ y tTT tTR tRR tT tR tTF tL r = recH1 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recH1R recH1CS recH1X recH1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_recH1R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(((-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ)))] 2 1 r = ratCoef [(((-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 / 2 : ℂ) * μ) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ) + (-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(((-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (((1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ) + (-1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (((1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ) + (-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (((-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ) + (-1 / 4 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((6 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-5 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((7 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 / 2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 / 2 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((8 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((2 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((3 : ℂ)) / ((2 - μ) * s)), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ) * s))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-4 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((2 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((10 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-20 : ℂ)) / ((2 - μ))), (0 : ℂ), (((10 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r + ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ) + (1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-6 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((4 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-3 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((13 : ℂ) + (1 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((-17 : ℂ) + (-1 / 2 : ℂ) * μ) / ((2 - μ))), (0 : ℂ), (((7 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_recH1R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-2 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-1 : ℂ)) / ((2 - μ))), (0 : ℂ), (((3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((-3 : ℂ)) / ((2 - μ))), (0 : ℂ), (((1 : ℂ)) / ((2 - μ)))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_recH1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 3) (hTR : TwistSmooth s tTR 2) (hT : TwistSmooth s tT 2) (hTF : TwistSmooth s tTF 3) :
    twist s (recH1R s μ y tTT tTR tRR tT tR tTF tL) r = recH2R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recH1R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [recH1X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num))]
  unfold recH2R recH1CS recH2CS recH1X recH2X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_recH1R_P s μ hr1 + (twist s (y) r) * twist_recH1R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_recH1R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_recH1R_P3 s μ hr1 + (tTR r) * twist_recH1R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_recH1R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_recH1R_qtr2 s μ hr1 + (tT r) * twist_recH1R_qt0 s μ hr1 + (twist s (tT) r) * twist_recH1R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_recH1R_qt2 s μ hr1 + (tTF r) * twist_recH1R_qT0 s μ hr1 + (twist s (tTF) r) * twist_recH1R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_recH1R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_recH1R_qT3 s μ hr1

theorem recH2R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    recH2R s μ y tTT tTR tRR tT tR tTF tL r = recH2 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold recH2R recH2CS recH2X recH2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `masterDefect0` over `r ^ (2 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def masterDefect0CS (s μ : ℂ) : Fin 12 → List ℂ :=
  ![[((-1 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ))], [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-8 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((8 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))]]

/-- Symbol functions of `masterDefect0`. -/
def masterDefect0X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 12 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 0 tTT, twistIter s 0 tTR, twistIter s 0 tRR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 0 tR, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF]

/-- `masterDefect0` as a rational-coefficient linear form in the twisted jets. -/
def masterDefect0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (masterDefect0CS s μ i) 2 2 r * masterDefect0X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `masterDefect1` over `r ^ (3 : ℕ) (r² − 1) ^ (3 : ℕ)`. -/
def masterDefect1CS (s μ : ℂ) : Fin 17 → List ℂ :=
  ![[((-2 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) * μ + (16 : ℂ) * s ^ (2 : ℕ))], [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-2 : ℂ) * μ + (4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((6 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) + (16 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((12 : ℂ) + (-12 : ℂ) * μ + (24 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((-4 : ℂ) + (4 : ℂ) * μ), (0 : ℂ), ((20 : ℂ) + (-8 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-20 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((22 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((10 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))]]

/-- Symbol functions of `masterDefect1`. -/
def masterDefect1X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 17 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 0 tTT, twistIter s 1 tTT, twistIter s 1 tTR, twistIter s 0 tRR, twistIter s 1 tRR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 1 tR, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF]

/-- `masterDefect1` as a rational-coefficient linear form in the twisted jets. -/
def masterDefect1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (masterDefect1CS s μ i) 3 3 r * masterDefect1X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `masterDefect2` over `r ^ (4 : ℕ) (r² − 1) ^ (4 : ℕ)`. -/
def masterDefect2CS (s μ : ℂ) : Fin 21 → List ℂ :=
  ![[((-6 : ℂ) * μ), (0 : ℂ), ((24 : ℂ) * μ), (0 : ℂ), ((-38 : ℂ) * μ + (-16 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((20 : ℂ) * μ + (-80 : ℂ) * s ^ (2 : ℕ))], [(0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-16 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) + (20 : ℂ) * μ + (-32 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((8 : ℂ) + (-8 : ℂ) * μ + (32 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((-1 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) + (3 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ) + (-3 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ) + (1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-4 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-24 : ℂ)), (0 : ℂ), ((-24 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((12 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((12 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((24 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((2 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((24 : ℂ)) / (s)), (0 : ℂ), (((-16 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-12 : ℂ)) / (s)), (0 : ℂ), (((12 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-12 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((24 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), ((8 : ℂ) + (-8 : ℂ) * μ), (0 : ℂ), ((-32 : ℂ) + (32 : ℂ) * μ), (0 : ℂ), ((48 : ℂ) + (-72 : ℂ) * μ + (-96 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-32 : ℂ) + (48 : ℂ) * μ + (-96 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((8 : ℂ))], [(0 : ℂ), (0 : ℂ), ((-8 : ℂ) + (8 : ℂ) * μ), (0 : ℂ), ((24 : ℂ) + (-40 : ℂ) * μ + (-16 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-64 : ℂ) + (56 : ℂ) * μ + (-32 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((56 : ℂ) + (-24 : ℂ) * μ + (48 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-8 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-32 : ℂ) + (12 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((56 : ℂ) + (-12 : ℂ) * μ + (16 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-32 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((8 : ℂ)), (0 : ℂ), ((-36 : ℂ)), (0 : ℂ), ((60 : ℂ)), (0 : ℂ), ((-44 : ℂ)), (0 : ℂ), ((12 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((2 : ℂ))]]

/-- Symbol functions of `masterDefect2`. -/
def masterDefect2X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 21 → ℝ → ℂ :=
  ![twistIter s 0 y, twistIter s 1 y, twistIter s 2 y, twistIter s 3 y, twistIter s 4 y, twistIter s 0 tTT, twistIter s 1 tTT, twistIter s 2 tTT, twistIter s 2 tTR, twistIter s 1 tRR, twistIter s 2 tRR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT, twistIter s 3 tT, twistIter s 2 tR, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 2 tTF, twistIter s 3 tTF, twistIter s 4 tTF]

/-- `masterDefect2` as a rational-coefficient linear form in the twisted jets. -/
def masterDefect2R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (masterDefect2CS s μ i) 4 4 r * masterDefect2X s y tTT tTR tRR tT tR tTF tL i r

theorem masterDefect0R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    masterDefect0R s μ y tTT tTR tRR tT tR tTF tL r = masterDefect0 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold masterDefect0R masterDefect0CS masterDefect0X masterDefect0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_masterDefect0R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((-1 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ))] 2 2 r = ratCoef [((-2 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) * μ + (16 : ℂ) * s ^ (2 : ℕ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((2 : ℂ))] 2 2 r + ratCoef [((-1 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ))] 2 2 r = ratCoef [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-2 : ℂ) * μ + (4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-2 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((2 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qtt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qtt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))] 2 2 r = (0 : ℂ) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qrr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qrr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((4 : ℂ))] 2 2 r = (0 : ℂ) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((4 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-8 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) + (16 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((12 : ℂ) + (-12 : ℂ) * μ + (24 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-4 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((8 : ℂ))] 2 2 r + ratCoef [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-8 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-4 : ℂ) + (4 : ℂ) * μ), (0 : ℂ), ((20 : ℂ) + (-8 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-20 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 2 2 r + ratCoef [(0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((8 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((22 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((10 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect0R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 2 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_masterDefect0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 3) (hTT : TwistSmooth s tTT 1) (hTR : TwistSmooth s tTR 1) (hRR : TwistSmooth s tRR 1) (hT : TwistSmooth s tT 2) (hR : TwistSmooth s tR 1) (hTF : TwistSmooth s tTF 3) :
    twist s (masterDefect0R s μ y tTT tTR tRR tT tR tTF tL) r = masterDefect1R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold masterDefect0R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [masterDefect0X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hTT r hr1 0 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hRR r hr1 0 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hR r hr1 0 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num))]
  unfold masterDefect1R masterDefect0CS masterDefect1CS masterDefect0X masterDefect1X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_masterDefect0R_P s μ hr1 + (twist s (y) r) * twist_masterDefect0R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_masterDefect0R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_masterDefect0R_P3 s μ hr1 + (tTT r) * twist_masterDefect0R_qtt0 s μ hr1 + (twist s (tTT) r) * twist_masterDefect0R_qtt1 s μ hr1 + (tTR r) * twist_masterDefect0R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_masterDefect0R_qtr1 s μ hr1 + (tRR r) * twist_masterDefect0R_qrr0 s μ hr1 + (twist s (tRR) r) * twist_masterDefect0R_qrr1 s μ hr1 + (tT r) * twist_masterDefect0R_qt0 s μ hr1 + (twist s (tT) r) * twist_masterDefect0R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_masterDefect0R_qt2 s μ hr1 + (tR r) * twist_masterDefect0R_qr0 s μ hr1 + (twist s (tR) r) * twist_masterDefect0R_qr1 s μ hr1 + (tTF r) * twist_masterDefect0R_qT0 s μ hr1 + (twist s (tTF) r) * twist_masterDefect0R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_masterDefect0R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_masterDefect0R_qT3 s μ hr1

theorem masterDefect1R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    masterDefect1R s μ y tTT tTR tRR tT tR tTF tL r = masterDefect1 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold masterDefect1R masterDefect1CS masterDefect1X masterDefect1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_masterDefect1R_P (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((-2 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) * μ + (16 : ℂ) * s ^ (2 : ℕ))] 3 3 r = ratCoef [((-6 : ℂ) * μ), (0 : ℂ), ((24 : ℂ) * μ), (0 : ℂ), ((-38 : ℂ) * μ + (-16 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((20 : ℂ) * μ + (-80 : ℂ) * s ^ (2 : ℕ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_P1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-2 : ℂ) * μ + (4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-2 : ℂ))] 3 3 r + ratCoef [((-2 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) * μ + (16 : ℂ) * s ^ (2 : ℕ))] 3 3 r = ratCoef [(0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-16 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) + (20 : ℂ) * μ + (-32 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((8 : ℂ) + (-8 : ℂ) * μ + (32 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_P2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-2 : ℂ) * μ + (4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-2 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-1 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) + (3 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ) + (-3 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ) + (1 : ℂ) * μ + (-4 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-4 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_P3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_P4 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((1 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qtt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-24 : ℂ)), (0 : ℂ), ((-24 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qtt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((12 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qtt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))] 3 3 r = (0 : ℂ) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((12 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((2 : ℂ)) / (s))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qrr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r = (0 : ℂ) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qrr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((24 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((4 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qrr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((2 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((24 : ℂ)) / (s)), (0 : ℂ), (((-16 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((-8 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-4 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((4 : ℂ)) / (s)), (0 : ℂ), (((-12 : ℂ)) / (s)), (0 : ℂ), (((12 : ℂ)) / (s)), (0 : ℂ), (((-4 : ℂ)) / (s))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qt3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (((2 : ℂ)) / (s)), (0 : ℂ), (((-6 : ℂ)) / (s)), (0 : ℂ), (((6 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (((-2 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-12 : ℂ)) / (s)), (0 : ℂ), (((8 : ℂ)) / (s)), (0 : ℂ), (((-2 : ℂ)) / (s))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 3 r = (0 : ℂ) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((24 : ℂ)), (0 : ℂ), ((-16 : ℂ)), (0 : ℂ), ((4 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) + (16 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((12 : ℂ) + (-12 : ℂ) * μ + (24 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-4 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), ((8 : ℂ) + (-8 : ℂ) * μ), (0 : ℂ), ((-32 : ℂ) + (32 : ℂ) * μ), (0 : ℂ), ((48 : ℂ) + (-72 : ℂ) * μ + (-96 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-32 : ℂ) + (48 : ℂ) * μ + (-96 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((8 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((-4 : ℂ) + (4 : ℂ) * μ), (0 : ℂ), ((20 : ℂ) + (-8 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-20 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) + (16 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((12 : ℂ) + (-12 : ℂ) * μ + (24 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-4 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-8 : ℂ) + (8 : ℂ) * μ), (0 : ℂ), ((24 : ℂ) + (-40 : ℂ) * μ + (-16 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-64 : ℂ) + (56 : ℂ) * μ + (-32 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((56 : ℂ) + (-24 : ℂ) * μ + (48 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-8 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qT2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((22 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((10 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), ((-4 : ℂ) + (4 : ℂ) * μ), (0 : ℂ), ((20 : ℂ) + (-8 : ℂ) * μ + (8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-20 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) + (-4 : ℂ) * μ), (0 : ℂ), ((-32 : ℂ) + (12 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((56 : ℂ) + (-12 : ℂ) * μ + (16 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((-32 : ℂ) + (4 : ℂ) * μ + (-8 : ℂ) * s ^ (2 : ℕ)), (0 : ℂ), ((4 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qT3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((22 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((10 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((8 : ℂ)), (0 : ℂ), ((-36 : ℂ)), (0 : ℂ), ((60 : ℂ)), (0 : ℂ), ((-44 : ℂ)), (0 : ℂ), ((12 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_masterDefect1R_qT4 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((2 : ℂ))] 3 3 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-8 : ℂ)), (0 : ℂ), ((2 : ℂ))] 4 4 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_masterDefect1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hy : TwistSmooth s y 4) (hTT : TwistSmooth s tTT 2) (hTR : TwistSmooth s tTR 2) (hRR : TwistSmooth s tRR 2) (hT : TwistSmooth s tT 3) (hR : TwistSmooth s tR 2) (hTF : TwistSmooth s tTF 4) :
    twist s (masterDefect1R s μ y tTT tTR tRR tT tR tTF tL) r = masterDefect2R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold masterDefect1R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [masterDefect1X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hy r hr1 0 (by norm_num) | exact hy r hr1 1 (by norm_num) | exact hy r hr1 2 (by norm_num) | exact hy r hr1 3 (by norm_num) | exact hTT r hr1 0 (by norm_num) | exact hTT r hr1 1 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hRR r hr1 0 (by norm_num) | exact hRR r hr1 1 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num) | exact hT r hr1 2 (by norm_num) | exact hR r hr1 1 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hTF r hr1 1 (by norm_num) | exact hTF r hr1 2 (by norm_num) | exact hTF r hr1 3 (by norm_num))]
  unfold masterDefect2R masterDefect1CS masterDefect2CS masterDefect1X masterDefect2X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (y r) * twist_masterDefect1R_P s μ hr1 + (twist s (y) r) * twist_masterDefect1R_P1 s μ hr1 + (twist s (twist s (y)) r) * twist_masterDefect1R_P2 s μ hr1 + (twist s (twist s (twist s (y))) r) * twist_masterDefect1R_P3 s μ hr1 + (twist s (twist s (twist s (twist s (y)))) r) * twist_masterDefect1R_P4 s μ hr1 + (tTT r) * twist_masterDefect1R_qtt0 s μ hr1 + (twist s (tTT) r) * twist_masterDefect1R_qtt1 s μ hr1 + (twist s (twist s (tTT)) r) * twist_masterDefect1R_qtt2 s μ hr1 + (twist s (tTR) r) * twist_masterDefect1R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_masterDefect1R_qtr2 s μ hr1 + (tRR r) * twist_masterDefect1R_qrr0 s μ hr1 + (twist s (tRR) r) * twist_masterDefect1R_qrr1 s μ hr1 + (twist s (twist s (tRR)) r) * twist_masterDefect1R_qrr2 s μ hr1 + (tT r) * twist_masterDefect1R_qt0 s μ hr1 + (twist s (tT) r) * twist_masterDefect1R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_masterDefect1R_qt2 s μ hr1 + (twist s (twist s (twist s (tT))) r) * twist_masterDefect1R_qt3 s μ hr1 + (twist s (tR) r) * twist_masterDefect1R_qr1 s μ hr1 + (twist s (twist s (tR)) r) * twist_masterDefect1R_qr2 s μ hr1 + (tTF r) * twist_masterDefect1R_qT0 s μ hr1 + (twist s (tTF) r) * twist_masterDefect1R_qT1 s μ hr1 + (twist s (twist s (tTF)) r) * twist_masterDefect1R_qT2 s μ hr1 + (twist s (twist s (twist s (tTF))) r) * twist_masterDefect1R_qT3 s μ hr1 + (twist s (twist s (twist s (twist s (tTF)))) r) * twist_masterDefect1R_qT4 s μ hr1

theorem masterDefect2R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    masterDefect2R s μ y tTT tTR tRR tT tR tTF tL r = masterDefect2 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold masterDefect2R masterDefect2CS masterDefect2X masterDefect2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `bianchiT0` over `r ^ (2 : ℕ) (r² − 1) ^ (1 : ℕ)`. -/
def bianchiT0CS (s μ : ℂ) : Fin 4 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))], [((-1 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)]]

/-- Symbol functions of `bianchiT0`. -/
def bianchiT0X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 4 → ℝ → ℂ :=
  ![twistIter s 0 tTT, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 0 tT]

/-- `bianchiT0` as a rational-coefficient linear form in the twisted jets. -/
def bianchiT0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiT0CS s μ i) 2 1 r * bianchiT0X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `bianchiT1` over `r ^ (3 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def bianchiT1CS (s μ : ℂ) : Fin 7 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((10 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((6 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))], [((-2 : ℂ) * μ), (0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ)], [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)]]

/-- Symbol functions of `bianchiT1`. -/
def bianchiT1X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 7 → ℝ → ℂ :=
  ![twistIter s 0 tTT, twistIter s 1 tTT, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 0 tT, twistIter s 1 tT]

/-- `bianchiT1` as a rational-coefficient linear form in the twisted jets. -/
def bianchiT1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiT1CS s μ i) 3 2 r * bianchiT1X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `bianchiT2` over `r ^ (4 : ℕ) (r² − 1) ^ (3 : ℕ)`. -/
def bianchiT2CS (s μ : ℂ) : Fin 10 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ) * s), (0 : ℂ), ((-12 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-8 : ℂ) * s), (0 : ℂ), ((8 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s), (0 : ℂ), ((4 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((18 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((10 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((30 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((8 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((1 : ℂ))], [((-6 : ℂ) * μ), (0 : ℂ), ((18 : ℂ) * μ), (0 : ℂ), ((-18 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ)], [(0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) * μ), (0 : ℂ), ((12 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) * μ)], [(0 : ℂ), (0 : ℂ), ((-1 : ℂ) * μ), (0 : ℂ), ((3 : ℂ) * μ), (0 : ℂ), ((-3 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)]]

/-- Symbol functions of `bianchiT2`. -/
def bianchiT2X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 10 → ℝ → ℂ :=
  ![twistIter s 0 tTT, twistIter s 1 tTT, twistIter s 2 tTT, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 2 tTR, twistIter s 3 tTR, twistIter s 0 tT, twistIter s 1 tT, twistIter s 2 tT]

/-- `bianchiT2` as a rational-coefficient linear form in the twisted jets. -/
def bianchiT2R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiT2CS s μ i) 4 3 r * bianchiT2X s y tTT tTR tRR tT tR tTF tL i r

theorem bianchiT0R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiT0R s μ y tTT tTR tRR tT tR tTF tL r = bianchiT0 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiT0R bianchiT0CS bianchiT0X bianchiT0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_bianchiT0R_qtt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s)] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) * s)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT0R_qtt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s)] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT0R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT0R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 1 r + ratCoef [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((10 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT0R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT0R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((-1 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 2 1 r = ratCoef [((-2 : ℂ) * μ), (0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT0R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [((-1 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 2 1 r = ratCoef [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_bianchiT0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r)  (hTT : TwistSmooth s tTT 1) (hTR : TwistSmooth s tTR 2) (hT : TwistSmooth s tT 1) :
    twist s (bianchiT0R s μ y tTT tTR tRR tT tR tTF tL) r = bianchiT1R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiT0R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [bianchiT0X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hTT r hr1 0 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hT r hr1 0 (by norm_num))]
  unfold bianchiT1R bianchiT0CS bianchiT1CS bianchiT0X bianchiT1X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (tTT r) * twist_bianchiT0R_qtt0 s μ hr1 + (twist s (tTT) r) * twist_bianchiT0R_qtt1 s μ hr1 + (tTR r) * twist_bianchiT0R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_bianchiT0R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_bianchiT0R_qtr2 s μ hr1 + (tT r) * twist_bianchiT0R_qt0 s μ hr1 + (twist s (tT) r) * twist_bianchiT0R_qt1 s μ hr1

theorem bianchiT1R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiT1R s μ y tTT tTR tRR tT tR tTF tL r = bianchiT1 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiT1R bianchiT1CS bianchiT1X bianchiT1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_bianchiT1R_qtt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) * s)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ) * s), (0 : ℂ), ((-12 : ℂ) * s)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qtt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 3 2 r + ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) * s)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-8 : ℂ) * s), (0 : ℂ), ((8 : ℂ) * s)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qtt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s), (0 : ℂ), ((4 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((12 : ℂ)), (0 : ℂ), ((-4 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((10 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 2 r + ratCoef [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((18 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((10 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qtr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r + ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((10 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((30 : ℂ)), (0 : ℂ), ((-26 : ℂ)), (0 : ℂ), ((8 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qtr3 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((1 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((-2 : ℂ) * μ), (0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ)] 3 2 r = ratCoef [((-6 : ℂ) * μ), (0 : ℂ), ((18 : ℂ) * μ), (0 : ℂ), ((-18 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 3 2 r + ratCoef [((-2 : ℂ) * μ), (0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ)] 3 2 r = ratCoef [(0 : ℂ), ((4 : ℂ) * μ), (0 : ℂ), ((-12 : ℂ) * μ), (0 : ℂ), ((12 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) * μ)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiT1R_qt2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-1 : ℂ) * μ), (0 : ℂ), ((3 : ℂ) * μ), (0 : ℂ), ((-3 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_bianchiT1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r)  (hTT : TwistSmooth s tTT 2) (hTR : TwistSmooth s tTR 3) (hT : TwistSmooth s tT 2) :
    twist s (bianchiT1R s μ y tTT tTR tRR tT tR tTF tL) r = bianchiT2R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiT1R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [bianchiT1X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hTT r hr1 0 (by norm_num) | exact hTT r hr1 1 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hTR r hr1 1 (by norm_num) | exact hTR r hr1 2 (by norm_num) | exact hT r hr1 0 (by norm_num) | exact hT r hr1 1 (by norm_num))]
  unfold bianchiT2R bianchiT1CS bianchiT2CS bianchiT1X bianchiT2X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (tTT r) * twist_bianchiT1R_qtt0 s μ hr1 + (twist s (tTT) r) * twist_bianchiT1R_qtt1 s μ hr1 + (twist s (twist s (tTT)) r) * twist_bianchiT1R_qtt2 s μ hr1 + (tTR r) * twist_bianchiT1R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_bianchiT1R_qtr1 s μ hr1 + (twist s (twist s (tTR)) r) * twist_bianchiT1R_qtr2 s μ hr1 + (twist s (twist s (twist s (tTR))) r) * twist_bianchiT1R_qtr3 s μ hr1 + (tT r) * twist_bianchiT1R_qt0 s μ hr1 + (twist s (tT) r) * twist_bianchiT1R_qt1 s μ hr1 + (twist s (twist s (tT)) r) * twist_bianchiT1R_qt2 s μ hr1

theorem bianchiT2R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiT2R s μ y tTT tTR tRR tT tR tTF tL r = bianchiT2 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiT2R bianchiT2CS bianchiT2X bianchiT2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `bianchiR0` over `r ^ (3 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def bianchiR0CS (s μ : ℂ) : Fin 6 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((9 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((5 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)], [((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))]]

/-- Symbol functions of `bianchiR0`. -/
def bianchiR0X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![twistIter s 0 tTT, twistIter s 0 tTR, twistIter s 0 tRR, twistIter s 1 tRR, twistIter s 0 tR, twistIter s 0 tL]

/-- `bianchiR0` as a rational-coefficient linear form in the twisted jets. -/
def bianchiR0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiR0CS s μ i) 3 2 r * bianchiR0X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `bianchiR1` over `r ^ (4 : ℕ) (r² − 1) ^ (3 : ℕ)`. -/
def bianchiR1CS (s μ : ℂ) : Fin 11 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((-3 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ) * s), (0 : ℂ), ((4 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s), (0 : ℂ), ((4 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((9 : ℂ)), (0 : ℂ), ((-13 : ℂ)), (0 : ℂ), ((5 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-13 : ℂ)), (0 : ℂ), ((27 : ℂ)), (0 : ℂ), ((-23 : ℂ)), (0 : ℂ), ((7 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((1 : ℂ))], [(0 : ℂ), ((2 : ℂ) * μ), (0 : ℂ), ((-6 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ)], [(0 : ℂ), (0 : ℂ), ((-1 : ℂ) * μ), (0 : ℂ), ((3 : ℂ) * μ), (0 : ℂ), ((-3 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)], [((-6 : ℂ)), (0 : ℂ), ((18 : ℂ)), (0 : ℂ), ((-18 : ℂ)), (0 : ℂ), ((6 : ℂ))], [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-2 : ℂ))]]

/-- Symbol functions of `bianchiR1`. -/
def bianchiR1X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 11 → ℝ → ℂ :=
  ![twistIter s 0 tTT, twistIter s 1 tTT, twistIter s 0 tTR, twistIter s 1 tTR, twistIter s 0 tRR, twistIter s 1 tRR, twistIter s 2 tRR, twistIter s 0 tR, twistIter s 1 tR, twistIter s 0 tL, twistIter s 1 tL]

/-- `bianchiR1` as a rational-coefficient linear form in the twisted jets. -/
def bianchiR1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiR1CS s μ i) 4 3 r * bianchiR1X s y tTT tTR tRR tT tR tTF tL i r

theorem bianchiR0R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiR0R s μ y tTT tTR tRR tT tR tTF tL r = bianchiR0 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiR0R bianchiR0CS bianchiR0X bianchiR0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_bianchiR0R_qtt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((-3 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qtt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((1 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qtr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-4 : ℂ) * s), (0 : ℂ), ((4 : ℂ) * s)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qtr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s), (0 : ℂ), ((4 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qrr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((9 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((5 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((9 : ℂ)), (0 : ℂ), ((-13 : ℂ)), (0 : ℂ), ((5 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qrr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r + ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((9 : ℂ)), (0 : ℂ), ((-12 : ℂ)), (0 : ℂ), ((5 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-13 : ℂ)), (0 : ℂ), ((27 : ℂ)), (0 : ℂ), ((-23 : ℂ)), (0 : ℂ), ((7 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qrr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-4 : ℂ)), (0 : ℂ), ((1 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 3 2 r = ratCoef [(0 : ℂ), ((2 : ℂ) * μ), (0 : ℂ), ((-6 : ℂ) * μ), (0 : ℂ), ((6 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), ((1 : ℂ) * μ), (0 : ℂ), ((-2 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 3 2 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-1 : ℂ) * μ), (0 : ℂ), ((3 : ℂ) * μ), (0 : ℂ), ((-3 : ℂ) * μ), (0 : ℂ), ((1 : ℂ) * μ)] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qL0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 3 2 r = ratCoef [((-6 : ℂ)), (0 : ℂ), ((18 : ℂ)), (0 : ℂ), ((-18 : ℂ)), (0 : ℂ), ((6 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiR0R_qL1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 3 2 r = ratCoef [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((6 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 4 3 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_bianchiR0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r)  (hTT : TwistSmooth s tTT 1) (hTR : TwistSmooth s tTR 1) (hRR : TwistSmooth s tRR 2) (hR : TwistSmooth s tR 1) (hL : TwistSmooth s tL 1) :
    twist s (bianchiR0R s μ y tTT tTR tRR tT tR tTF tL) r = bianchiR1R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiR0R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [bianchiR0X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hTT r hr1 0 (by norm_num) | exact hTR r hr1 0 (by norm_num) | exact hRR r hr1 0 (by norm_num) | exact hRR r hr1 1 (by norm_num) | exact hR r hr1 0 (by norm_num) | exact hL r hr1 0 (by norm_num))]
  unfold bianchiR1R bianchiR0CS bianchiR1CS bianchiR0X bianchiR1X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (tTT r) * twist_bianchiR0R_qtt0 s μ hr1 + (twist s (tTT) r) * twist_bianchiR0R_qtt1 s μ hr1 + (tTR r) * twist_bianchiR0R_qtr0 s μ hr1 + (twist s (tTR) r) * twist_bianchiR0R_qtr1 s μ hr1 + (tRR r) * twist_bianchiR0R_qrr0 s μ hr1 + (twist s (tRR) r) * twist_bianchiR0R_qrr1 s μ hr1 + (twist s (twist s (tRR)) r) * twist_bianchiR0R_qrr2 s μ hr1 + (tR r) * twist_bianchiR0R_qr0 s μ hr1 + (twist s (tR) r) * twist_bianchiR0R_qr1 s μ hr1 + (tL r) * twist_bianchiR0R_qL0 s μ hr1 + (twist s (tL) r) * twist_bianchiR0R_qL1 s μ hr1

theorem bianchiR1R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiR1R s μ y tTT tTR tRR tT tR tTF tL r = bianchiR1 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiR1R bianchiR1CS bianchiR1X bianchiR1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Horner coefficient lists of `bianchiAng0` over `r ^ (2 : ℕ) (r² − 1) ^ (1 : ℕ)`. -/
def bianchiAng0CS (s μ : ℂ) : Fin 5 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))], [((1 : ℂ) + (-1 / 2 : ℂ) * μ), (0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ)], [((-1 : ℂ)), (0 : ℂ), ((1 : ℂ))]]

/-- Symbol functions of `bianchiAng0`. -/
def bianchiAng0X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 5 → ℝ → ℂ :=
  ![twistIter s 0 tT, twistIter s 0 tR, twistIter s 1 tR, twistIter s 0 tTF, twistIter s 0 tL]

/-- `bianchiAng0` as a rational-coefficient linear form in the twisted jets. -/
def bianchiAng0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiAng0CS s μ i) 2 1 r * bianchiAng0X s y tTT tTR tRR tT tR tTF tL i r

/-- Horner coefficient lists of `bianchiAng1` over `r ^ (3 : ℕ) (r² − 1) ^ (2 : ℕ)`. -/
def bianchiAng1CS (s μ : ℂ) : Fin 9 → List ℂ :=
  ![[(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) * s)], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)], [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))], [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((10 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((6 : ℂ))], [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))], [((2 : ℂ) + (-1 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) + (2 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-1 : ℂ) * μ)], [(0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-1 : ℂ) * μ), (0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ)], [((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))], [(0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))]]

/-- Symbol functions of `bianchiAng1`. -/
def bianchiAng1X (s : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Fin 9 → ℝ → ℂ :=
  ![twistIter s 0 tT, twistIter s 1 tT, twistIter s 0 tR, twistIter s 1 tR, twistIter s 2 tR, twistIter s 0 tTF, twistIter s 1 tTF, twistIter s 0 tL, twistIter s 1 tL]

/-- `bianchiAng1` as a rational-coefficient linear form in the twisted jets. -/
def bianchiAng1R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∑ i, ratCoef (bianchiAng1CS s μ i) 3 2 r * bianchiAng1X s y tTT tTR tRR tT tR tTF tL i r

theorem bianchiAng0R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiAng0R s μ y tTT tTR tRR tT tR tTF tL r = bianchiAng0 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiAng0R bianchiAng0CS bianchiAng0X bianchiAng0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

private theorem twist_bianchiAng0R_qt0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s)] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((4 : ℂ) * s)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qt1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ) * s)] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((2 : ℂ) * s), (0 : ℂ), ((-2 : ℂ) * s)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qr0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qr1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 1 r + ratCoef [(0 : ℂ), ((2 : ℂ)), (0 : ℂ), ((-6 : ℂ)), (0 : ℂ), ((4 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((10 : ℂ)), (0 : ℂ), ((-14 : ℂ)), (0 : ℂ), ((6 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qr2 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), (0 : ℂ), (0 : ℂ), ((-1 : ℂ)), (0 : ℂ), ((3 : ℂ)), (0 : ℂ), ((-3 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qT0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((1 : ℂ) + (-1 / 2 : ℂ) * μ), (0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ)] 2 1 r = ratCoef [((2 : ℂ) + (-1 : ℂ) * μ), (0 : ℂ), ((-4 : ℂ) + (2 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-1 : ℂ) * μ)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qT1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [((1 : ℂ) + (-1 / 2 : ℂ) * μ), (0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ)] 2 1 r = ratCoef [(0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ), (0 : ℂ), ((2 : ℂ) + (-1 : ℂ) * μ), (0 : ℂ), ((-1 : ℂ) + (1 / 2 : ℂ) * μ)] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qL0 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoefDeriv [((-1 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 1 r = ratCoef [((-2 : ℂ)), (0 : ℂ), ((4 : ℂ)), (0 : ℂ), ((-2 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

private theorem twist_bianchiAng0R_qL1 (s μ : ℂ) {r : ℝ} (hr1 : 1 < r) :
    ratCoef [((-1 : ℂ)), (0 : ℂ), ((1 : ℂ))] 2 1 r = ratCoef [(0 : ℂ), ((1 : ℂ)), (0 : ℂ), ((-2 : ℂ)), (0 : ℂ), ((1 : ℂ))] 3 2 r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  simp only [ratCoef, ratCoefDeriv, horner, hornerDeriv, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ]
  field_simp
  ring

theorem twist_bianchiAng0R (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r)  (hT : TwistSmooth s tT 1) (hR : TwistSmooth s tR 2) (hTF : TwistSmooth s tTF 1) (hL : TwistSmooth s tL 1) :
    twist s (bianchiAng0R s μ y tTT tTR tRR tT tR tTF tL) r = bianchiAng1R s μ y tTT tTR tRR tT tR tTF tL r := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiAng0R
  rw [twist_linear s _ _ _ _ hr hf (by
    intro i
    fin_cases i
    all_goals simp only [bianchiAng0X, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.mk_one, Fin.isValue, Fin.zero_eta]
    all_goals first | exact hT r hr1 0 (by norm_num) | exact hR r hr1 0 (by norm_num) | exact hR r hr1 1 (by norm_num) | exact hTF r hr1 0 (by norm_num) | exact hL r hr1 0 (by norm_num))]
  unfold bianchiAng1R bianchiAng0CS bianchiAng1CS bianchiAng0X bianchiAng1X
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, twistIter_succ, twistIter_zero, add_zero]
  linear_combination (tT r) * twist_bianchiAng0R_qt0 s μ hr1 + (twist s (tT) r) * twist_bianchiAng0R_qt1 s μ hr1 + (tR r) * twist_bianchiAng0R_qr0 s μ hr1 + (twist s (tR) r) * twist_bianchiAng0R_qr1 s μ hr1 + (twist s (twist s (tR)) r) * twist_bianchiAng0R_qr2 s μ hr1 + (tTF r) * twist_bianchiAng0R_qT0 s μ hr1 + (twist s (tTF) r) * twist_bianchiAng0R_qT1 s μ hr1 + (tL r) * twist_bianchiAng0R_qL0 s μ hr1 + (twist s (tL) r) * twist_bianchiAng0R_qL1 s μ hr1

theorem bianchiAng1R_eq (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) {r : ℝ} (hr1 : 1 < r) (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0) :
    bianchiAng1R s μ y tTT tTR tRR tT tR tTF tL r = bianchiAng1 s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  unfold bianchiAng1R bianchiAng1CS bianchiAng1X bianchiAng1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, ratCoef, ratCoefDeriv, horner, hornerDeriv, twistIter_succ, twistIter_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.cast_succ, add_zero]
  field_simp
  ring

/-- Hypotheses of the field-level reconstruction: differentiability of the twisted jets, the sourced
master equation and the three Bianchi identities of the source on the exterior. -/
structure SourcedMasterData (s μ : ℂ) (y tTT tTR tRR tT tR tTF tL : ℝ → ℂ) : Prop where
  smooth_y : TwistSmooth s y 4
  smooth_tTT : TwistSmooth s tTT 4
  smooth_tTR : TwistSmooth s tTR 4
  smooth_tRR : TwistSmooth s tRR 4
  smooth_tT : TwistSmooth s tT 4
  smooth_tR : TwistSmooth s tR 4
  smooth_tTF : TwistSmooth s tTF 4
  smooth_tL : TwistSmooth s tL 4
  master : ∀ r : ℝ, 1 < r → masterDefect0R s μ y tTT tTR tRR tT tR tTF tL r = 0
  bianchiT : ∀ r : ℝ, 1 < r → bianchiT0R s μ y tTT tTR tRR tT tR tTF tL r = 0
  bianchiR : ∀ r : ℝ, 1 < r → bianchiR0R s μ y tTT tTR tRR tT tR tTF tL r = 0
  bianchiAng : ∀ r : ℝ, 1 < r → bianchiAng0R s μ y tTT tTR tRR tT tR tTF tL r = 0

theorem SourcedMasterData.masterDefect1 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) : ∀ r : ℝ, 1 < r → masterDefect1R s μ y tTT tTR tRR tT tR tTF tL r = 0 := by
  intro r hr1
  rw [← twist_masterDefect0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTT.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tRR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tR.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num))]
  exact twist_eventuallyEq_zero s (by
    filter_upwards [exterior_eventually hr1] with r' hr' using h.master r' hr')

theorem SourcedMasterData.masterDefect2 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) : ∀ r : ℝ, 1 < r → masterDefect2R s μ y tTT tTR tRR tT tR tTF tL r = 0 := by
  intro r hr1
  rw [← twist_masterDefect1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTT.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tRR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tR.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num))]
  exact twist_eventuallyEq_zero s (by
    filter_upwards [exterior_eventually hr1] with r' hr' using h.masterDefect1 r' hr')

theorem SourcedMasterData.bianchiT1 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) : ∀ r : ℝ, 1 < r → bianchiT1R s μ y tTT tTR tRR tT tR tTF tL r = 0 := by
  intro r hr1
  rw [← twist_bianchiT0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_tTT.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num))]
  exact twist_eventuallyEq_zero s (by
    filter_upwards [exterior_eventually hr1] with r' hr' using h.bianchiT r' hr')

theorem SourcedMasterData.bianchiT2 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) : ∀ r : ℝ, 1 < r → bianchiT2R s μ y tTT tTR tRR tT tR tTF tL r = 0 := by
  intro r hr1
  rw [← twist_bianchiT1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_tTT.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num))]
  exact twist_eventuallyEq_zero s (by
    filter_upwards [exterior_eventually hr1] with r' hr' using h.bianchiT1 r' hr')

theorem SourcedMasterData.bianchiR1 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) : ∀ r : ℝ, 1 < r → bianchiR1R s μ y tTT tTR tRR tT tR tTF tL r = 0 := by
  intro r hr1
  rw [← twist_bianchiR0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_tTT.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tRR.mono (by norm_num)) (h.smooth_tR.mono (by norm_num)) (h.smooth_tL.mono (by norm_num))]
  exact twist_eventuallyEq_zero s (by
    filter_upwards [exterior_eventually hr1] with r' hr' using h.bianchiR r' hr')

theorem SourcedMasterData.bianchiAng1 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) : ∀ r : ℝ, 1 < r → bianchiAng1R s μ y tTT tTR tRR tT tR tTF tL r = 0 := by
  intro r hr1
  rw [← twist_bianchiAng0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_tT.mono (by norm_num)) (h.smooth_tR.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)) (h.smooth_tL.mono (by norm_num))]
  exact twist_eventuallyEq_zero s (by
    filter_upwards [exterior_eventually hr1] with r' hr' using h.bianchiAng r' hr')

theorem SourcedMasterData.twist2_recF0 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r = recF02R s μ y tTT tTR tRR tT tR tTF tL r := by
  rw [twist_congr s (g := twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) (h := recF01R s μ y tTT tTR tRR tT tR tTF tL) (by
    filter_upwards [exterior_eventually hr1] with r' hr'
    exact twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr' (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)))]
  exact twist_recF01R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num))

theorem SourcedMasterData.twist2_recF1 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r = recF12R s μ y tTT tTR tRR tT tR tTF tL r := by
  rw [twist_congr s (g := twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) (h := recF11R s μ y tTT tTR tRR tT tR tTF tL) (by
    filter_upwards [exterior_eventually hr1] with r' hr'
    exact twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr' (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)))]
  exact twist_recF11R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num))

theorem SourcedMasterData.twist2_recF2 {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r = recF22R s μ y tTT tTR tRR tT tR tTF tL r := by
  rw [twist_congr s (g := twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) (h := recF21R s μ y tTT tTR tRR tT tR tTF tL) (by
    filter_upwards [exterior_eventually hr1] with r' hr'
    exact twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr' (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)))]
  exact twist_recF21R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num))

theorem SourcedMasterData.twist2_recH {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ}
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r = recH2R s μ y tTT tTR tRR tT tR tTF tL r := by
  rw [twist_congr s (g := twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) (h := recH1R s μ y tTT tTR tRR tT tR tTF tL) (by
    filter_upwards [exterior_eventually hr1] with r' hr'
    exact twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr' (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)))]
  exact twist_recH1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num))

/-- The sourced harmonic `tt` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_TT {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicTT s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tTT r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_TT s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  rw [← bianchiT0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ] at hrec
  rw [h.bianchiT r hr1] at hrec
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

/-- The sourced harmonic `tr` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_TR {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicTR s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tTR r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_TR s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

/-- The sourced harmonic `rr` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_RR {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicRR s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tRR r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_RR s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  rw [← masterDefect0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← masterDefect1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiR0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiAng0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ] at hrec
  rw [h.master r hr1, h.masterDefect1 r hr1, h.bianchiT r hr1, h.bianchiT1 r hr1, h.bianchiR r hr1, h.bianchiAng r hr1] at hrec
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

/-- The sourced harmonic `t` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_T {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicT s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tT r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_T s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

/-- The sourced harmonic `r` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_R {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicR s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tR r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_R s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  rw [← masterDefect0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← masterDefect1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiR0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiAng0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ] at hrec
  rw [h.master r hr1, h.masterDefect1 r hr1, h.bianchiT r hr1, h.bianchiT1 r hr1, h.bianchiR r hr1, h.bianchiAng r hr1] at hrec
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

/-- The sourced harmonic `T` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_TF {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicTF s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tTF r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_TF s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

/-- The sourced harmonic `L` equation holds for the twisted two-jets of the reconstructed radial functions. -/
theorem sourced_equation_L {s μ : ℂ} {y tTT tTR tRR tT tR tTF tL : ℝ → ℂ} (hs : s ≠ 0) (hμ : (2 : ℂ) - μ ≠ 0)
    (h : SourcedMasterData s μ y tTT tTR tRR tT tR tTF tL) {r : ℝ} (hr1 : 1 < r) :
    harmonicL s r μ (recF0R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF0R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF1R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF1R s μ y tTT tTR tRR tT tR tTF tL)) r) (recF2R s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recF2R s μ y tTT tTR tRR tT tR tTF tL)) r) (recHR s μ y tTT tTR tRR tT tR tTF tL r) (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL) r) (twist s (twist s (recHR s μ y tTT tTR tRR tT tR tTF tL)) r) + tL r = 0 := by
  have hr := (exterior_ne r hr1).1
  have hf := (exterior_ne r hr1).2
  rw [twist_recF0R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF0 hr1,
    twist_recF1R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF1 hr1,
    twist_recF2R s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recF2 hr1,
    twist_recHR s μ y tTT tTR tRR tT tR tTF tL hr1 (h.smooth_y.mono (by norm_num)) (h.smooth_tTR.mono (by norm_num)) (h.smooth_tT.mono (by norm_num)) (h.smooth_tTF.mono (by norm_num)), h.twist2_recH hr1]
  rw [recF0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF01R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF02R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF11R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF12R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF21R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recF22R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recHR_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, recH2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ]
  have hrec := reconstruction_L s r μ (twistIter s 0 y r) (twistIter s 1 y r) (twistIter s 2 y r) (twistIter s 3 y r) (twistIter s 4 y r) (twistIter s 0 tTT r) (twistIter s 1 tTT r) (twistIter s 2 tTT r) (twistIter s 3 tTT r) (twistIter s 4 tTT r) (twistIter s 0 tTR r) (twistIter s 1 tTR r) (twistIter s 2 tTR r) (twistIter s 3 tTR r) (twistIter s 4 tTR r) (twistIter s 5 tTR r) (twistIter s 0 tRR r) (twistIter s 1 tRR r) (twistIter s 2 tRR r) (twistIter s 3 tRR r) (twistIter s 4 tRR r) (twistIter s 5 tRR r) (twistIter s 0 tT r) (twistIter s 1 tT r) (twistIter s 2 tT r) (twistIter s 3 tT r) (twistIter s 4 tT r) (twistIter s 0 tR r) (twistIter s 1 tR r) (twistIter s 2 tR r) (twistIter s 3 tR r) (twistIter s 4 tR r) (twistIter s 5 tR r) (twistIter s 0 tTF r) (twistIter s 1 tTF r) (twistIter s 2 tTF r) (twistIter s 3 tTF r) (twistIter s 4 tTF r) (twistIter s 0 tL r) (twistIter s 1 tL r) (twistIter s 2 tL r) (twistIter s 3 tL r) (twistIter s 4 tL r) hs hr hf hμ
  rw [← masterDefect0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← masterDefect1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← masterDefect2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiT2R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiR0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiR1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiAng0R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ, ← bianchiAng1R_eq s μ y tTT tTR tRR tT tR tTF tL hr1 hs hμ] at hrec
  rw [h.master r hr1, h.masterDefect1 r hr1, h.masterDefect2 r hr1, h.bianchiT r hr1, h.bianchiT1 r hr1, h.bianchiT2 r hr1, h.bianchiR r hr1, h.bianchiR1 r hr1, h.bianchiAng r hr1, h.bianchiAng1 r hr1] at hrec
  simp only [twistIter_zero] at hrec ⊢
  linear_combination hrec

end
end RHTower.D4BMScalarStream
