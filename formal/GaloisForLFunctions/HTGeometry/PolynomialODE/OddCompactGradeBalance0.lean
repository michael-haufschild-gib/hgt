import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactCubicGrade

/-!
# Drift-degree balances of the corrected determinant (0)

At every drift degree the substituted determinant plus the weighted head
product equals the cubic minorant plus the nonnegative remainder.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- Drift degree 0 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance0 (u t w : ℝ) :
    (oddCompactShiftedDetPart0Grade0 u t w +
      oddCompactShiftedDetPart1Grade0 u t w +
      oddCompactShiftedDetPart2Grade0 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart0Grade0 u t w) =
      (oddCompactCubicMinorantGrade0 u t w) +
      (oddCompactRemainderPart0Grade0 u t w +
      oddCompactRemainderPart1Grade0 u t w +
      oddCompactRemainderPart2Grade0 u t w +
      oddCompactRemainderPart3Grade0 u t w) := by
  unfold oddCompactShiftedDetPart0Grade0 oddCompactShiftedDetPart1Grade0 oddCompactShiftedDetPart2Grade0 oddCompactShiftedHeadLowPart0Grade0 oddCompactRemainderPart0Grade0 oddCompactRemainderPart1Grade0 oddCompactRemainderPart2Grade0 oddCompactRemainderPart3Grade0 oddCompactCubicMinorantGrade0
  ring

/-- Drift degree 1 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance1 (u t w : ℝ) :
    (oddCompactShiftedDetPart2Grade1 u t w +
      oddCompactShiftedDetPart3Grade1 u t w +
      oddCompactShiftedDetPart4Grade1 u t w +
      oddCompactShiftedDetPart5Grade1 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart0Grade1 u t w +
      oddCompactShiftedHeadLowPart1Grade1 u t w) =
      (oddCompactCubicMinorantGrade1 u t w) +
      (oddCompactRemainderPart3Grade1 u t w +
      oddCompactRemainderPart4Grade1 u t w +
      oddCompactRemainderPart5Grade1 u t w +
      oddCompactRemainderPart6Grade1 u t w +
      oddCompactRemainderPart7Grade1 u t w) := by
  unfold oddCompactShiftedDetPart2Grade1 oddCompactShiftedDetPart3Grade1 oddCompactShiftedDetPart4Grade1 oddCompactShiftedDetPart5Grade1 oddCompactShiftedHeadLowPart0Grade1 oddCompactShiftedHeadLowPart1Grade1 oddCompactRemainderPart3Grade1 oddCompactRemainderPart4Grade1 oddCompactRemainderPart5Grade1 oddCompactRemainderPart6Grade1 oddCompactRemainderPart7Grade1 oddCompactCubicMinorantGrade1
  ring

/-- Drift degree 2 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance2 (u t w : ℝ) :
    (oddCompactShiftedDetPart5Grade2 u t w +
      oddCompactShiftedDetPart6Grade2 u t w +
      oddCompactShiftedDetPart7Grade2 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart0Grade2 u t w +
      oddCompactShiftedHeadLowPart1Grade2 u t w +
      oddCompactShiftedHeadLowPart2Grade2 u t w) =
      (oddCompactCubicMinorantGrade2 u t w) +
      (oddCompactRemainderPart7Grade2 u t w +
      oddCompactRemainderPart8Grade2 u t w +
      oddCompactRemainderPart9Grade2 u t w +
      oddCompactRemainderPart10Grade2 u t w) := by
  unfold oddCompactShiftedDetPart5Grade2 oddCompactShiftedDetPart6Grade2 oddCompactShiftedDetPart7Grade2 oddCompactShiftedHeadLowPart0Grade2 oddCompactShiftedHeadLowPart1Grade2 oddCompactShiftedHeadLowPart2Grade2 oddCompactRemainderPart7Grade2 oddCompactRemainderPart8Grade2 oddCompactRemainderPart9Grade2 oddCompactRemainderPart10Grade2 oddCompactCubicMinorantGrade2
  ring

/-- Drift degree 3 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance3 (u t w : ℝ) :
    (oddCompactShiftedDetPart7Grade3 u t w +
      oddCompactShiftedDetPart8Grade3 u t w +
      oddCompactShiftedDetPart9Grade3 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart0Grade3 u t w +
      oddCompactShiftedHeadLowPart1Grade3 u t w +
      oddCompactShiftedHeadLowPart2Grade3 u t w) =
      (oddCompactCubicMinorantGrade3 u t w) +
      (oddCompactRemainderPart10Grade3 u t w +
      oddCompactRemainderPart11Grade3 u t w +
      oddCompactRemainderPart12Grade3 u t w +
      oddCompactRemainderPart13Grade3 u t w +
      oddCompactRemainderPart14Grade3 u t w +
      oddCompactRemainderPart15Grade3 u t w +
      oddCompactRemainderPart16Grade3 u t w +
      oddCompactRemainderPart17Grade3 u t w +
      oddCompactRemainderPart18Grade3 u t w +
      oddCompactRemainderPart19Grade3 u t w +
      oddCompactRemainderPart20Grade3 u t w +
      oddCompactRemainderPart21Grade3 u t w +
      oddCompactRemainderPart22Grade3 u t w +
      oddCompactRemainderPart23Grade3 u t w +
      oddCompactRemainderPart24Grade3 u t w +
      oddCompactRemainderPart25Grade3 u t w +
      oddCompactRemainderPart26Grade3 u t w +
      oddCompactRemainderPart27Grade3 u t w +
      oddCompactRemainderPart28Grade3 u t w +
      oddCompactRemainderPart29Grade3 u t w +
      oddCompactRemainderPart30Grade3 u t w +
      oddCompactRemainderPart31Grade3 u t w +
      oddCompactRemainderPart32Grade3 u t w +
      oddCompactRemainderPart33Grade3 u t w +
      oddCompactRemainderPart34Grade3 u t w +
      oddCompactRemainderPart35Grade3 u t w +
      oddCompactRemainderPart36Grade3 u t w +
      oddCompactRemainderPart37Grade3 u t w +
      oddCompactRemainderPart38Grade3 u t w +
      oddCompactRemainderPart39Grade3 u t w +
      oddCompactRemainderPart40Grade3 u t w +
      oddCompactRemainderPart41Grade3 u t w +
      oddCompactRemainderPart42Grade3 u t w +
      oddCompactRemainderPart43Grade3 u t w +
      oddCompactRemainderPart44Grade3 u t w +
      oddCompactRemainderPart45Grade3 u t w +
      oddCompactRemainderPart46Grade3 u t w +
      oddCompactRemainderPart47Grade3 u t w +
      oddCompactRemainderPart48Grade3 u t w +
      oddCompactRemainderPart49Grade3 u t w +
      oddCompactRemainderPart50Grade3 u t w) := by
  unfold oddCompactShiftedDetPart7Grade3 oddCompactShiftedDetPart8Grade3 oddCompactShiftedDetPart9Grade3 oddCompactShiftedHeadLowPart0Grade3 oddCompactShiftedHeadLowPart1Grade3 oddCompactShiftedHeadLowPart2Grade3 oddCompactRemainderPart10Grade3 oddCompactRemainderPart11Grade3 oddCompactRemainderPart12Grade3 oddCompactRemainderPart13Grade3 oddCompactRemainderPart14Grade3 oddCompactRemainderPart15Grade3 oddCompactRemainderPart16Grade3 oddCompactRemainderPart17Grade3 oddCompactRemainderPart18Grade3 oddCompactRemainderPart19Grade3 oddCompactRemainderPart20Grade3 oddCompactRemainderPart21Grade3 oddCompactRemainderPart22Grade3 oddCompactRemainderPart23Grade3 oddCompactRemainderPart24Grade3 oddCompactRemainderPart25Grade3 oddCompactRemainderPart26Grade3 oddCompactRemainderPart27Grade3 oddCompactRemainderPart28Grade3 oddCompactRemainderPart29Grade3 oddCompactRemainderPart30Grade3 oddCompactRemainderPart31Grade3 oddCompactRemainderPart32Grade3 oddCompactRemainderPart33Grade3 oddCompactRemainderPart34Grade3 oddCompactRemainderPart35Grade3 oddCompactRemainderPart36Grade3 oddCompactRemainderPart37Grade3 oddCompactRemainderPart38Grade3 oddCompactRemainderPart39Grade3 oddCompactRemainderPart40Grade3 oddCompactRemainderPart41Grade3 oddCompactRemainderPart42Grade3 oddCompactRemainderPart43Grade3 oddCompactRemainderPart44Grade3 oddCompactRemainderPart45Grade3 oddCompactRemainderPart46Grade3 oddCompactRemainderPart47Grade3 oddCompactRemainderPart48Grade3 oddCompactRemainderPart49Grade3 oddCompactRemainderPart50Grade3 oddCompactCubicMinorantGrade3
  ring

/-- Drift degree 4 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance4 (u t w : ℝ) :
    (oddCompactShiftedDetPart10Grade4 u t w +
      oddCompactShiftedDetPart11Grade4 u t w +
      oddCompactShiftedDetPart12Grade4 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart0Grade4 u t w +
      oddCompactShiftedHeadLowPart1Grade4 u t w +
      oddCompactShiftedHeadLowPart2Grade4 u t w +
      oddCompactShiftedHeadLowPart3Grade4 u t w) =
      (oddCompactRemainderPart14Grade4 u t w +
      oddCompactRemainderPart15Grade4 u t w +
      oddCompactRemainderPart16Grade4 u t w +
      oddCompactRemainderPart17Grade4 u t w) := by
  unfold oddCompactShiftedDetPart10Grade4 oddCompactShiftedDetPart11Grade4 oddCompactShiftedDetPart12Grade4 oddCompactShiftedHeadLowPart0Grade4 oddCompactShiftedHeadLowPart1Grade4 oddCompactShiftedHeadLowPart2Grade4 oddCompactShiftedHeadLowPart3Grade4 oddCompactRemainderPart14Grade4 oddCompactRemainderPart15Grade4 oddCompactRemainderPart16Grade4 oddCompactRemainderPart17Grade4
  ring

/-- Drift degree 5 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance5 (u t w : ℝ) :
    (oddCompactShiftedDetPart12Grade5 u t w +
      oddCompactShiftedDetPart13Grade5 u t w +
      oddCompactShiftedDetPart14Grade5 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart0Grade5 u t w +
      oddCompactShiftedHeadLowPart1Grade5 u t w +
      oddCompactShiftedHeadLowPart2Grade5 u t w +
      oddCompactShiftedHeadLowPart3Grade5 u t w) =
      (oddCompactRemainderPart17Grade5 u t w +
      oddCompactRemainderPart18Grade5 u t w +
      oddCompactRemainderPart19Grade5 u t w +
      oddCompactRemainderPart20Grade5 u t w +
      oddCompactRemainderPart21Grade5 u t w) := by
  unfold oddCompactShiftedDetPart12Grade5 oddCompactShiftedDetPart13Grade5 oddCompactShiftedDetPart14Grade5 oddCompactShiftedHeadLowPart0Grade5 oddCompactShiftedHeadLowPart1Grade5 oddCompactShiftedHeadLowPart2Grade5 oddCompactShiftedHeadLowPart3Grade5 oddCompactRemainderPart17Grade5 oddCompactRemainderPart18Grade5 oddCompactRemainderPart19Grade5 oddCompactRemainderPart20Grade5 oddCompactRemainderPart21Grade5
  ring

/-- Drift degree 6 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance6 (u t w : ℝ) :
    (oddCompactShiftedDetPart14Grade6 u t w +
      oddCompactShiftedDetPart15Grade6 u t w +
      oddCompactShiftedDetPart16Grade6 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart1Grade6 u t w +
      oddCompactShiftedHeadLowPart2Grade6 u t w +
      oddCompactShiftedHeadLowPart3Grade6 u t w +
      oddCompactShiftedHeadLowPart4Grade6 u t w) =
      (oddCompactRemainderPart21Grade6 u t w +
      oddCompactRemainderPart22Grade6 u t w +
      oddCompactRemainderPart23Grade6 u t w +
      oddCompactRemainderPart24Grade6 u t w) := by
  unfold oddCompactShiftedDetPart14Grade6 oddCompactShiftedDetPart15Grade6 oddCompactShiftedDetPart16Grade6 oddCompactShiftedHeadLowPart1Grade6 oddCompactShiftedHeadLowPart2Grade6 oddCompactShiftedHeadLowPart3Grade6 oddCompactShiftedHeadLowPart4Grade6 oddCompactRemainderPart21Grade6 oddCompactRemainderPart22Grade6 oddCompactRemainderPart23Grade6 oddCompactRemainderPart24Grade6
  ring

/-- Drift degree 7 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance7 (u t w : ℝ) :
    (oddCompactShiftedDetPart16Grade7 u t w +
      oddCompactShiftedDetPart17Grade7 u t w +
      oddCompactShiftedDetPart18Grade7 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart2Grade7 u t w +
      oddCompactShiftedHeadLowPart3Grade7 u t w +
      oddCompactShiftedHeadLowPart4Grade7 u t w) =
      (oddCompactRemainderPart24Grade7 u t w +
      oddCompactRemainderPart25Grade7 u t w +
      oddCompactRemainderPart26Grade7 u t w +
      oddCompactRemainderPart27Grade7 u t w) := by
  unfold oddCompactShiftedDetPart16Grade7 oddCompactShiftedDetPart17Grade7 oddCompactShiftedDetPart18Grade7 oddCompactShiftedHeadLowPart2Grade7 oddCompactShiftedHeadLowPart3Grade7 oddCompactShiftedHeadLowPart4Grade7 oddCompactRemainderPart24Grade7 oddCompactRemainderPart25Grade7 oddCompactRemainderPart26Grade7 oddCompactRemainderPart27Grade7
  ring

/-- Drift degree 8 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance8 (u t w : ℝ) :
    (oddCompactShiftedDetPart18Grade8 u t w +
      oddCompactShiftedDetPart19Grade8 u t w +
      oddCompactShiftedDetPart20Grade8 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart2Grade8 u t w +
      oddCompactShiftedHeadLowPart3Grade8 u t w +
      oddCompactShiftedHeadLowPart4Grade8 u t w) =
      (oddCompactRemainderPart27Grade8 u t w +
      oddCompactRemainderPart28Grade8 u t w +
      oddCompactRemainderPart29Grade8 u t w +
      oddCompactRemainderPart30Grade8 u t w) := by
  unfold oddCompactShiftedDetPart18Grade8 oddCompactShiftedDetPart19Grade8 oddCompactShiftedDetPart20Grade8 oddCompactShiftedHeadLowPart2Grade8 oddCompactShiftedHeadLowPart3Grade8 oddCompactShiftedHeadLowPart4Grade8 oddCompactRemainderPart27Grade8 oddCompactRemainderPart28Grade8 oddCompactRemainderPart29Grade8 oddCompactRemainderPart30Grade8
  ring

/-- Drift degree 9 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance9 (u t w : ℝ) :
    (oddCompactShiftedDetPart20Grade9 u t w +
      oddCompactShiftedDetPart21Grade9 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart3Grade9 u t w +
      oddCompactShiftedHeadLowPart4Grade9 u t w) =
      (oddCompactRemainderPart30Grade9 u t w +
      oddCompactRemainderPart31Grade9 u t w +
      oddCompactRemainderPart32Grade9 u t w +
      oddCompactRemainderPart33Grade9 u t w) := by
  unfold oddCompactShiftedDetPart20Grade9 oddCompactShiftedDetPart21Grade9 oddCompactShiftedHeadLowPart3Grade9 oddCompactShiftedHeadLowPart4Grade9 oddCompactRemainderPart30Grade9 oddCompactRemainderPart31Grade9 oddCompactRemainderPart32Grade9 oddCompactRemainderPart33Grade9
  ring

/-- Drift degree 10 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance10 (u t w : ℝ) :
    (oddCompactShiftedDetPart21Grade10 u t w +
      oddCompactShiftedDetPart22Grade10 u t w +
      oddCompactShiftedDetPart23Grade10 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart3Grade10 u t w +
      oddCompactShiftedHeadLowPart4Grade10 u t w +
      oddCompactShiftedHeadLowPart5Grade10 u t w) =
      (oddCompactRemainderPart33Grade10 u t w +
      oddCompactRemainderPart34Grade10 u t w +
      oddCompactRemainderPart35Grade10 u t w) := by
  unfold oddCompactShiftedDetPart21Grade10 oddCompactShiftedDetPart22Grade10 oddCompactShiftedDetPart23Grade10 oddCompactShiftedHeadLowPart3Grade10 oddCompactShiftedHeadLowPart4Grade10 oddCompactShiftedHeadLowPart5Grade10 oddCompactRemainderPart33Grade10 oddCompactRemainderPart34Grade10 oddCompactRemainderPart35Grade10
  ring

/-- Drift degree 11 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance11 (u t w : ℝ) :
    (oddCompactShiftedDetPart23Grade11 u t w +
      oddCompactShiftedDetPart24Grade11 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart4Grade11 u t w +
      oddCompactShiftedHeadLowPart5Grade11 u t w) =
      (oddCompactRemainderPart35Grade11 u t w +
      oddCompactRemainderPart36Grade11 u t w +
      oddCompactRemainderPart37Grade11 u t w) := by
  unfold oddCompactShiftedDetPart23Grade11 oddCompactShiftedDetPart24Grade11 oddCompactShiftedHeadLowPart4Grade11 oddCompactShiftedHeadLowPart5Grade11 oddCompactRemainderPart35Grade11 oddCompactRemainderPart36Grade11 oddCompactRemainderPart37Grade11
  ring

/-- Drift degree 12 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance12 (u t w : ℝ) :
    (oddCompactShiftedDetPart24Grade12 u t w +
      oddCompactShiftedDetPart25Grade12 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart4Grade12 u t w +
      oddCompactShiftedHeadLowPart5Grade12 u t w) =
      (oddCompactRemainderPart37Grade12 u t w +
      oddCompactRemainderPart38Grade12 u t w +
      oddCompactRemainderPart39Grade12 u t w) := by
  unfold oddCompactShiftedDetPart24Grade12 oddCompactShiftedDetPart25Grade12 oddCompactShiftedHeadLowPart4Grade12 oddCompactShiftedHeadLowPart5Grade12 oddCompactRemainderPart37Grade12 oddCompactRemainderPart38Grade12 oddCompactRemainderPart39Grade12
  ring

/-- Drift degree 13 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance13 (u t w : ℝ) :
    (oddCompactShiftedDetPart25Grade13 u t w +
      oddCompactShiftedDetPart26Grade13 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart4Grade13 u t w +
      oddCompactShiftedHeadLowPart5Grade13 u t w) =
      (oddCompactRemainderPart39Grade13 u t w +
      oddCompactRemainderPart40Grade13 u t w +
      oddCompactRemainderPart41Grade13 u t w) := by
  unfold oddCompactShiftedDetPart25Grade13 oddCompactShiftedDetPart26Grade13 oddCompactShiftedHeadLowPart4Grade13 oddCompactShiftedHeadLowPart5Grade13 oddCompactRemainderPart39Grade13 oddCompactRemainderPart40Grade13 oddCompactRemainderPart41Grade13
  ring

/-- Drift degree 14 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance14 (u t w : ℝ) :
    (oddCompactShiftedDetPart26Grade14 u t w +
      oddCompactShiftedDetPart27Grade14 u t w +
      oddCompactShiftedDetPart28Grade14 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart4Grade14 u t w +
      oddCompactShiftedHeadLowPart5Grade14 u t w) =
      (oddCompactRemainderPart41Grade14 u t w +
      oddCompactRemainderPart42Grade14 u t w) := by
  unfold oddCompactShiftedDetPart26Grade14 oddCompactShiftedDetPart27Grade14 oddCompactShiftedDetPart28Grade14 oddCompactShiftedHeadLowPart4Grade14 oddCompactShiftedHeadLowPart5Grade14 oddCompactRemainderPart41Grade14 oddCompactRemainderPart42Grade14
  ring

/-- Drift degree 15 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance15 (u t w : ℝ) :
    (oddCompactShiftedDetPart28Grade15 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart5Grade15 u t w) =
      (oddCompactRemainderPart42Grade15 u t w +
      oddCompactRemainderPart43Grade15 u t w +
      oddCompactRemainderPart44Grade15 u t w) := by
  unfold oddCompactShiftedDetPart28Grade15 oddCompactShiftedHeadLowPart5Grade15 oddCompactRemainderPart42Grade15 oddCompactRemainderPart43Grade15 oddCompactRemainderPart44Grade15
  ring

/-- Drift degree 16 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance16 (u t w : ℝ) :
    (oddCompactShiftedDetPart28Grade16 u t w +
      oddCompactShiftedDetPart29Grade16 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart5Grade16 u t w) =
      (oddCompactRemainderPart44Grade16 u t w +
      oddCompactRemainderPart45Grade16 u t w) := by
  unfold oddCompactShiftedDetPart28Grade16 oddCompactShiftedDetPart29Grade16 oddCompactShiftedHeadLowPart5Grade16 oddCompactRemainderPart44Grade16 oddCompactRemainderPart45Grade16
  ring

/-- Drift degree 17 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance17 (u t w : ℝ) :
    (oddCompactShiftedDetPart29Grade17 u t w +
      oddCompactShiftedDetPart30Grade17 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart5Grade17 u t w) =
      (oddCompactRemainderPart45Grade17 u t w +
      oddCompactRemainderPart46Grade17 u t w) := by
  unfold oddCompactShiftedDetPart29Grade17 oddCompactShiftedDetPart30Grade17 oddCompactShiftedHeadLowPart5Grade17 oddCompactRemainderPart45Grade17 oddCompactRemainderPart46Grade17
  ring

/-- Drift degree 18 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance18 (u t w : ℝ) :
    (oddCompactShiftedDetPart30Grade18 u t w +
      oddCompactShiftedDetPart31Grade18 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart5Grade18 u t w) =
      (oddCompactRemainderPart46Grade18 u t w) := by
  unfold oddCompactShiftedDetPart30Grade18 oddCompactShiftedDetPart31Grade18 oddCompactShiftedHeadLowPart5Grade18 oddCompactRemainderPart46Grade18
  ring

/-- Drift degree 19 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance19 (u t w : ℝ) :
    (oddCompactShiftedDetPart31Grade19 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart5Grade19 u t w) =
      (oddCompactRemainderPart46Grade19 u t w +
      oddCompactRemainderPart47Grade19 u t w) := by
  unfold oddCompactShiftedDetPart31Grade19 oddCompactShiftedHeadLowPart5Grade19 oddCompactRemainderPart46Grade19 oddCompactRemainderPart47Grade19
  ring

/-- Drift degree 20 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance20 (u t w : ℝ) :
    (oddCompactShiftedDetPart31Grade20 u t w) +
      1000000000*(oddCompactShiftedHeadLowPart5Grade20 u t w) =
      (oddCompactRemainderPart47Grade20 u t w +
      oddCompactRemainderPart48Grade20 u t w) := by
  unfold oddCompactShiftedDetPart31Grade20 oddCompactShiftedHeadLowPart5Grade20 oddCompactRemainderPart47Grade20 oddCompactRemainderPart48Grade20
  ring

/-- Drift degree 21 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance21 (u t w : ℝ) :
    (oddCompactShiftedDetPart32Grade21 u t w) =
      (oddCompactRemainderPart48Grade21 u t w) := by
  unfold oddCompactShiftedDetPart32Grade21 oddCompactRemainderPart48Grade21
  ring

/-- Drift degree 22 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance22 (u t w : ℝ) :
    (oddCompactShiftedDetPart32Grade22 u t w) =
      (oddCompactRemainderPart48Grade22 u t w +
      oddCompactRemainderPart49Grade22 u t w) := by
  unfold oddCompactShiftedDetPart32Grade22 oddCompactRemainderPart48Grade22 oddCompactRemainderPart49Grade22
  ring

/-- Drift degree 23 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance23 (u t w : ℝ) :
    (oddCompactShiftedDetPart32Grade23 u t w) =
      (oddCompactRemainderPart49Grade23 u t w) := by
  unfold oddCompactShiftedDetPart32Grade23 oddCompactRemainderPart49Grade23
  ring

/-- Drift degree 24 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance24 (u t w : ℝ) :
    (oddCompactShiftedDetPart32Grade24 u t w +
      oddCompactShiftedDetPart33Grade24 u t w) =
      (oddCompactRemainderPart49Grade24 u t w) := by
  unfold oddCompactShiftedDetPart32Grade24 oddCompactShiftedDetPart33Grade24 oddCompactRemainderPart49Grade24
  ring

/-- Drift degree 25 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance25 (u t w : ℝ) :
    (oddCompactShiftedDetPart33Grade25 u t w) =
      (oddCompactRemainderPart49Grade25 u t w) := by
  unfold oddCompactShiftedDetPart33Grade25 oddCompactRemainderPart49Grade25
  ring

/-- Drift degree 26 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance26 (u t w : ℝ) :
    (oddCompactShiftedDetPart33Grade26 u t w) =
      (oddCompactRemainderPart49Grade26 u t w) := by
  unfold oddCompactShiftedDetPart33Grade26 oddCompactRemainderPart49Grade26
  ring

/-- Drift degree 27 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance27 (u t w : ℝ) :
    (oddCompactShiftedDetPart33Grade27 u t w) =
      (oddCompactRemainderPart49Grade27 u t w +
      oddCompactRemainderPart50Grade27 u t w) := by
  unfold oddCompactShiftedDetPart33Grade27 oddCompactRemainderPart49Grade27 oddCompactRemainderPart50Grade27
  ring

/-- Drift degree 28 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance28 (u t w : ℝ) :
    (oddCompactShiftedDetPart33Grade28 u t w) =
      (oddCompactRemainderPart50Grade28 u t w) := by
  unfold oddCompactShiftedDetPart33Grade28 oddCompactRemainderPart50Grade28
  ring

/-- Drift degree 30 of the complete corrected decomposition. -/
theorem oddCompactGradeBalance30 (u t w : ℝ) :
    (oddCompactShiftedDetPart33Grade30 u t w) =
      (oddCompactRemainderPart50Grade30 u t w) := by
  unfold oddCompactShiftedDetPart33Grade30 oddCompactRemainderPart50Grade30
  ring

end
end HTGeometry
