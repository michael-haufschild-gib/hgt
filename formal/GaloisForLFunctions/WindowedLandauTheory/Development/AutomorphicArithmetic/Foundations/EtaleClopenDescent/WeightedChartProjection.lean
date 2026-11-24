import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedChartComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechRestriction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.MixedCechCupBoundary

/-! Extracting chart degree zero in the Koszul direction and restricting
the Koszul indices both commute with the weighted differential. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH.WeightedChartSystem

variable {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
  [AddCommGroup E] [Module k E] [LinearOrder κ]
  {d : ℕ} (T : WeightedChartSystem k d S E)

/-- The Čech cochain at the empty Koszul index set. -/
def chartPart (a : Finset (ChartPair d ⊕ₗ κ) → E) (I : Finset (ChartPair d)) : E :=
  a (uni I (∅ : Finset κ))

theorem chartPart_mem {n : κ → ℕ × ℕ} {z : κ → S} {p : ℤ}
    {a : Finset (ChartPair d ⊕ₗ κ) → E} (ha : a ∈ (T.complex n z).C p) :
    chartPart a ∈ (mixedCech T.M).C p := by
  refine acx_mem_terms_iff.mpr (fun I => ?_)
  have h := acx_mem_terms_iff.mp ha (uni I (∅ : Finset κ))
  simpa only [card_uni, Finset.card_empty, add_zero, lft_uni, rgt_uni,
    mixedCoefficients, scaledCoefficients, Finset.prod_empty, Units.val_one, map_one,
    Module.End.one_eq_id, Submodule.map_id, chartPart] using h

theorem chartPart_wd (z : κ → S) (a : Finset (ChartPair d ⊕ₗ κ) → E) :
    chartPart (wd (T.weights z) a) = deltaL k (ChartPair d) E (chartPart a) := by
  funext I
  rw [chartPart, wd_uni, wd_apply]
  rw [wd_apply, Finset.sum_empty, smul_zero, add_zero, deltaL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [weights, ofLex_toLex, Sum.elim_inl, map_one, Module.End.one_apply, chartPart]

/-- Projection to Koszul degree zero sends cocycles to chart cocycles. -/
theorem chartPart_mem_cycles {n : κ → ℕ × ℕ} {z : κ → S} {p : ℤ}
    {a : Finset (ChartPair d ⊕ₗ κ) → E} (ha : a ∈ (T.complex n z).Z p) :
    chartPart a ∈ (mixedCech T.M).Z p := by
  refine ⟨T.chartPart_mem ha.1, ?_⟩
  change wd (1 : ChartPair d → Module.End k E) (chartPart a) = 0
  rw [wd_one, ← T.chartPart_wd z, show wd (T.weights z) a = 0 from ha.2]
  rfl

/-- A primitive projects to a primitive in the chart complex. -/
theorem chartPart_mem_boundaries {n : κ → ℕ × ℕ} {z : κ → S} {p : ℤ}
    {a : Finset (ChartPair d ⊕ₗ κ) → E} (ha : a ∈ (T.complex n z).B p) :
    chartPart a ∈ (mixedCech T.M).B p := by
  obtain ⟨v, hv, hda⟩ := ha
  refine ⟨chartPart v, T.chartPart_mem hv, ?_⟩
  change wd (1 : ChartPair d → Module.End k E) (chartPart v) = chartPart a
  rw [wd_one, ← T.chartPart_wd z, show wd (T.weights z) v = a from hda]

/-- Restrict the Koszul direction of the cochain along an order embedding. -/
def restrictKoszulIndices {κ' : Type} [LinearOrder κ'] (e : κ' ↪o κ)
    (a : Finset (ChartPair d ⊕ₗ κ) → E) (s : Finset (ChartPair d ⊕ₗ κ')) : E :=
  a (uni (lft s) ((rgt s).map e.toEmbedding))

theorem restrictKoszulIndices_wd {κ' : Type} [LinearOrder κ'] (e : κ' ↪o κ)
    (z : κ → S) (a : Finset (ChartPair d ⊕ₗ κ) → E) :
    wd (T.weights fun l => z (e l)) (restrictKoszulIndices e a) =
      restrictKoszulIndices e (wd (T.weights z) a) := by
  funext s
  obtain ⟨I, L, rfl⟩ : ∃ I L, s = uni I L := ⟨lft s, rgt s, (uni_lft_rgt s).symm⟩
  rw [wd_uni, restrictKoszulIndices, lft_uni, rgt_uni, wd_uni]
  simp only [restrictKoszulIndices, lft_uni, rgt_uni, weights, ofLex_toLex,
    Sum.elim_inl, Sum.elim_inr, map_one]
  rw [wd_orderEmbedding e (fun j => T.act (z j)) (fun K => a (uni I K)) L]

/-- On a nonempty chart intersection the right column is its
homogeneous Koszul column. -/
theorem rightColumn_eq (n : κ → ℕ × ℕ) (z : κ → S) (I : Finset (ChartPair d))
    (hI : (lft I).Nonempty) (hJ : (rgt I).Nonempty) :
    rightColumn (fun s => T.mixedCoefficients n (rgt s) (lft s)) (T.weights z) I =
      T.columnComplex n z (lft I) (rgt I) := by
  have h : (lft I).Nonempty ∧ (rgt I).Nonempty := ⟨hI, hJ⟩
  simp only [rightColumn, columnComplex, mixedCoefficients, lft_uni, rgt_uni,
    if_pos h, weights, ofLex_toLex, Sum.elim_inr]

/-- Exactness of each nonzero chart column gives exactness of all the
right columns in the same degree. -/
theorem rightColumn_exact_of_columnExact (n : κ → ℕ × ℕ) (z : κ → S) (m : ℤ)
    (hex : ∀ I J, I.Nonempty → J.Nonempty → ∀ p < m,
      (T.columnComplex n z I J).Z p ≤ (T.columnComplex n z I J).B p) :
    ∀ I p, p < m →
      let C := rightColumn (fun s => T.mixedCoefficients n (rgt s) (lft s)) (T.weights z) I
      C.Z p ≤ C.B p := by
  intro I p hp
  by_cases h : (lft I).Nonempty ∧ (rgt I).Nonempty
  · dsimp only
    rw [T.rightColumn_eq n z I h.1 h.2]
    exact hex (lft I) (rgt I) h.1 h.2 p hp
  · dsimp only
    intro a ha
    have hz : a = 0 := funext fun L => (Submodule.mem_bot k).mp (by
      simpa only [mixedCoefficients, lft_uni, rgt_uni, if_neg h, ite_self] using
        acx_mem_terms_iff.mp ha.1 L)
    rw [hz]
    exact zero_mem _

/-- Column exactness gives exactness of the right filtration of the
joined weighted complex. -/
theorem filtrationExact_of_columnExact [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S) (m : ℤ)
    (hex : ∀ I J, I.Nonempty → J.Nonempty → ∀ p < m,
      (T.columnComplex n z I J).Z p ≤ (T.columnComplex n z I J).B p) :
    QEx (fun s => T.mixedCoefficients n (rgt s) (lft s)) (T.weights z) rightIndices m :=
  qEx_of_rightColumn_exact _ _ m (T.rightColumn_exact_of_columnExact n z m hex)

end GlobalTheory.WH.WeightedChartSystem
