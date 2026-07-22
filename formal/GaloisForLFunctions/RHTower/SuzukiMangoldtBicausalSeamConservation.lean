import GaloisForLFunctions.HTGeometry.BicausalDisplacementOverlap
import GaloisForLFunctions.RHTower.SuzukiMangoldtLogHaarTransport

open Set MeasureTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-!
# Exact seam conservation for Suzuki--Mangoldt transport

The sharp and unconditional Mangoldt cell families are contiguous cumulative-mass partitions with
different past/future shifts.  This module identifies the exact aggregate overlap created when the
future family is used below a cutoff and the past family above it.
-/

/-! ## Sharp width-two aggregates -/

/-- Aggregate sharp future target through cutoff `j`. -/
def mangoldtLogHaarSharpFutureAggregate (j : ℕ) : Set ℝ :=
  bicausalLeftTarget (mangoldtLogHaarMass 1 + 2) (mangoldtLogHaarMass j) 2

/-- Aggregate sharp past target after cutoff `j`, truncated at `N`. -/
def mangoldtLogHaarSharpPastAggregate (j N : ℕ) : Set ℝ :=
  bicausalRightTarget (mangoldtLogHaarMass j) (mangoldtLogHaarMass N)

/-- Exact duplicate-capacity seam for the sharp Mangoldt transport. -/
def mangoldtLogHaarSharpBicausalSeam (j : ℕ) : Set ℝ :=
  bicausalSeam (mangoldtLogHaarMass j) 2

/-- Every sharp future cell below the cutoff lies in the sharp future aggregate. -/
theorem mangoldtLogHaarSharpFutureCell_subset_aggregate
    {n j : ℕ} (hn : 2 ≤ n) (hnj : n ≤ j) :
    mangoldtLogHaarSharpFutureCell n ⊆ mangoldtLogHaarSharpFutureAggregate j := by
  have hfirst := monotone_mangoldtLogHaarMass (show 1 ≤ n - 1 by omega)
  have hlast := monotone_mangoldtLogHaarMass hnj
  intro x hx
  rw [mangoldtLogHaarSharpFutureCell, Set.mem_Ioc] at hx
  rw [mangoldtLogHaarSharpFutureAggregate, bicausalLeftTarget, Set.mem_Ioc]
  constructor <;> linarith

/-- Every sharp past cell above the cutoff lies in the sharp past aggregate. -/
theorem mangoldtLogHaarSharpPastCell_subset_aggregate
    {j n N : ℕ} (hjn : j < n) (hnN : n ≤ N) :
    mangoldtLogHaarSharpPastCell n ⊆ mangoldtLogHaarSharpPastAggregate j N := by
  have hfirst := monotone_mangoldtLogHaarMass (show j ≤ n - 1 by omega)
  have hlast := monotone_mangoldtLogHaarMass hnN
  intro x hx
  rw [mangoldtLogHaarSharpPastCell, Set.mem_Ioc] at hx
  rw [mangoldtLogHaarSharpPastAggregate, bicausalRightTarget, Set.mem_Ioc]
  exact ⟨lt_of_le_of_lt hfirst hx.1, hx.2.trans hlast⟩

/-- Sharp future/past aggregates double-use exactly the width-two seam. -/
theorem mangoldtLogHaarSharpFutureAggregate_inter_pastAggregate
    {j N : ℕ}
    (hleft : mangoldtLogHaarMass 1 + 2 ≤ mangoldtLogHaarMass j)
    (hright : mangoldtLogHaarMass j + 2 ≤ mangoldtLogHaarMass N) :
    mangoldtLogHaarSharpFutureAggregate j ∩ mangoldtLogHaarSharpPastAggregate j N =
      mangoldtLogHaarSharpBicausalSeam j :=
  bicausalLeftTarget_inter_rightTarget hleft hright

/-- The sharp duplicate-capacity seam has exact real volume two. -/
theorem volume_mangoldtLogHaarSharpBicausalSeam (j : ℕ) :
    (volume (mangoldtLogHaarSharpBicausalSeam j)).toReal = 2 :=
  volume_bicausalSeam (by norm_num)

/-- Exact sharp mixed-target integral ledger: the only surcharge is the width-two seam. -/
theorem mangoldtLogHaarSharp_bicausal_intervalIntegral_conservation
    {j N : ℕ} {Phi : ℝ → ℝ}
    (hleft : mangoldtLogHaarMass 1 + 2 ≤ mangoldtLogHaarMass j)
    (hright : mangoldtLogHaarMass j + 2 ≤ mangoldtLogHaarMass N)
    (hint : IntervalIntegrable Phi volume (mangoldtLogHaarMass 1 + 2)
      (mangoldtLogHaarMass N)) :
    (∫ x : ℝ in (mangoldtLogHaarMass 1 + 2)..(mangoldtLogHaarMass j + 2), Phi x) +
        (∫ x : ℝ in (mangoldtLogHaarMass j)..(mangoldtLogHaarMass N), Phi x) =
      (∫ x : ℝ in (mangoldtLogHaarMass 1 + 2)..(mangoldtLogHaarMass N), Phi x) +
        (∫ x : ℝ in (mangoldtLogHaarMass j)..(mangoldtLogHaarMass j + 2), Phi x) :=
  bicausal_intervalIntegral_conservation hleft (by norm_num) hright hint

/-! ## Fully unconditional Mertens-width aggregates -/

/-- Aggregate unconditional future target through cutoff `j`. -/
def mangoldtLogHaarFutureAggregate (j : ℕ) : Set ℝ :=
  bicausalLeftTarget
    (mangoldtLogHaarMass 1 + mangoldtLogHaarMertensRadius + 2)
    (mangoldtLogHaarMass j - mangoldtLogHaarMertensRadius)
    mangoldtLogHaarTransportWidth

/-- Aggregate unconditional past target after cutoff `j`, truncated at `N`. -/
def mangoldtLogHaarPastAggregate (j N : ℕ) : Set ℝ :=
  bicausalRightTarget
    (mangoldtLogHaarMass j - mangoldtLogHaarMertensRadius)
    (mangoldtLogHaarMass N - mangoldtLogHaarMertensRadius)

/-- Exact duplicate-capacity seam for the unconditional transport. -/
def mangoldtLogHaarBicausalSeam (j : ℕ) : Set ℝ :=
  bicausalSeam
    (mangoldtLogHaarMass j - mangoldtLogHaarMertensRadius)
    mangoldtLogHaarTransportWidth

/-- Widening the one-sided transport enlarges the seam by exactly the same amount. -/
theorem mangoldtLogHaar_bicausalSeam_endpoint_gap (j : ℕ) :
    (mangoldtLogHaarMass j + mangoldtLogHaarMertensRadius + 2) -
        (mangoldtLogHaarMass j - mangoldtLogHaarMertensRadius) =
      mangoldtLogHaarTransportWidth := by
  rw [mangoldtLogHaarTransportWidth]
  ring

/-- Every unconditional future cell below the cutoff lies in its future aggregate. -/
theorem mangoldtLogHaarFutureCell_subset_aggregate
    {n j : ℕ} (hn : 2 ≤ n) (hnj : n ≤ j) :
    mangoldtLogHaarFutureCell n ⊆ mangoldtLogHaarFutureAggregate j := by
  have hfirst := monotone_mangoldtLogHaarMass (show 1 ≤ n - 1 by omega)
  have hlast := monotone_mangoldtLogHaarMass hnj
  intro x hx
  rw [mangoldtLogHaarFutureCell, Set.mem_Ioc] at hx
  rw [mangoldtLogHaarFutureAggregate, bicausalLeftTarget, Set.mem_Ioc,
    mangoldtLogHaarTransportWidth]
  constructor <;> linarith

/-- Every unconditional past cell above the cutoff lies in its past aggregate. -/
theorem mangoldtLogHaarPastCell_subset_aggregate
    {j n N : ℕ} (hjn : j < n) (hnN : n ≤ N) :
    mangoldtLogHaarPastCell n ⊆ mangoldtLogHaarPastAggregate j N := by
  have hfirst := monotone_mangoldtLogHaarMass (show j ≤ n - 1 by omega)
  have hlast := monotone_mangoldtLogHaarMass hnN
  intro x hx
  rw [mangoldtLogHaarPastCell, Set.mem_Ioc] at hx
  rw [mangoldtLogHaarPastAggregate, bicausalRightTarget, Set.mem_Ioc]
  exact ⟨lt_of_le_of_lt (by linarith) hx.1, by linarith⟩

/-- The unconditional aggregate overlap is exactly its full transport displacement. -/
theorem mangoldtLogHaarFutureAggregate_inter_pastAggregate
    {j N : ℕ}
    (hleft : mangoldtLogHaarMass 1 + mangoldtLogHaarMertensRadius + 2 ≤
      mangoldtLogHaarMass j - mangoldtLogHaarMertensRadius)
    (hright : mangoldtLogHaarMass j + mangoldtLogHaarMertensRadius + 2 ≤
      mangoldtLogHaarMass N - mangoldtLogHaarMertensRadius) :
    mangoldtLogHaarFutureAggregate j ∩ mangoldtLogHaarPastAggregate j N =
      mangoldtLogHaarBicausalSeam j := by
  apply bicausalLeftTarget_inter_rightTarget hleft
  rw [mangoldtLogHaarTransportWidth]
  linarith

/-- The unconditional duplicate seam has volume equal to the formalized transport width. -/
theorem volume_mangoldtLogHaarBicausalSeam (j : ℕ) :
    (volume (mangoldtLogHaarBicausalSeam j)).toReal =
      mangoldtLogHaarTransportWidth :=
  volume_bicausalSeam mangoldtLogHaarTransportWidth_nonneg

end RHTower
