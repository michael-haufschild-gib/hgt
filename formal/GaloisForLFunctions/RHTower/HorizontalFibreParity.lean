import GaloisForLFunctions.RHTower.HorizontalOddFiberCharging
import GaloisForLFunctions.RHTower.OrbitParityOffLine
import GaloisForLFunctions.RHTower.WindowRelation
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Parity of a horizontal Xi fibre

The involution `s \mapsto 1 - \bar s` preserves the ordinate, preserves the Xi divisor with
multiplicity, and has the critical line as its exact fixed-point set.  On a single ordinate it
therefore pairs off the off-line copies, so the total fibre multiplicity has the same parity as the
critical-line multiplicity:

```text
h(γ) ≡ k(γ)   (mod 2).
```

In particular the odd-fibre ordinates of `HorizontalOddFiberCharging.lean` are exactly the
critical-line Xi zeros of odd order — the objects a sign-change detector produces.
-/

open Complex Set


noncomputable section

namespace RHTower

theorem feSchwarz_eq_lineReflect (z : ℂ) : feSchwarz z = lineReflect z := rfl

/-- **Fibre parity.**  The total multiplicity of a horizontal Xi fibre has the same parity as the
critical-line multiplicity at that ordinate: the off-line copies pair off under the
functional-equation/Schwarz involution, whose only fixed points are on the critical line. -/
theorem xiHorizontalMultiplicity_odd_iff (t : ℝ) :
    Odd (xiHorizontalMultiplicity t) ↔ Odd ((analyticOrderAt xi (linePt t)).toNat) := by
  classical
  set S : Finset ℂ := stripHeightFinset t with hS
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun z => z.re = 1 / 2)
    (fun z => (analyticOrderAt xi z).toNat)
  have hcrit : ∑ z ∈ S.filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat
      = (analyticOrderAt xi (linePt t)).toNat := by
    by_cases hz : xi (linePt t) = 0
    · have hmem : linePt t ∈ S := by
        rw [hS, mem_stripHeightFinset]
        refine ⟨?_, ?_, ?_, hz⟩
        · rw [linePt_re]; norm_num
        · rw [linePt_re]; norm_num
        · rw [linePt_im]
      have hsing : S.filter (fun z => z.re = 1 / 2) = {linePt t} := by
        ext w
        rw [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hw, hwre⟩
          have hwim : w.im = t := (mem_stripHeightFinset.mp hw).2.2.1
          exact Complex.ext (by rw [hwre, linePt_re]) (by rw [hwim, linePt_im])
        · rintro rfl
          exact ⟨hmem, linePt_re t⟩
      rw [hsing, Finset.sum_singleton]
    · have hempty : S.filter (fun z => z.re = 1 / 2) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro w hw hwre
        have hwim : w.im = t := (mem_stripHeightFinset.mp hw).2.2.1
        have hzero : xi w = 0 := (mem_stripHeightFinset.mp hw).2.2.2
        have : w = linePt t := Complex.ext (by rw [hwre, linePt_re]) (by rw [hwim, linePt_im])
        rw [this] at hzero
        exact hz hzero
      have hord : (analyticOrderAt xi (linePt t)).toNat = 0 := by
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]
        rfl
      rw [hempty, Finset.sum_empty, hord]
  have hoff : Even (∑ z ∈ S.filter (fun z => ¬ z.re = 1 / 2), (analyticOrderAt xi z).toNat) := by
    refine even_sum_of_offCritical (fun z => (analyticOrderAt xi z).toNat) _ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      refine ⟨?_, ?_⟩
      · rw [hS] at hz ⊢
        exact lineReflect_mem_stripHeightFinset hz.1
      · rw [feSchwarz_re]
        intro h
        exact hz.2 (by linarith)
    · intro z
      rw [feSchwarz_eq_lineReflect]
      exact congrArg ENat.toNat (xi_orderAt_lineReflect z)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  have hsum : xiHorizontalMultiplicity t
      = (analyticOrderAt xi (linePt t)).toNat
        + ∑ z ∈ S.filter (fun z => ¬ z.re = 1 / 2), (analyticOrderAt xi z).toNat := by
    rw [xiHorizontalMultiplicity, ← hS, ← hsplit, hcrit]
  rw [hsum]
  obtain ⟨m, hm⟩ := hoff
  rw [hm]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j - m, by omega⟩
  · rintro ⟨j, hj⟩; exact ⟨j + m, by omega⟩

/-- The odd-fibre ordinates are exactly the critical-line Xi zeros of odd order. -/
theorem mem_xiOddFiber_iff {T : ℝ} {z : ℂ} :
    (z ∈ (stripFinsetPos T).filter
        (fun z => z.re = 1 / 2 ∧ Odd (xiHorizontalMultiplicity z.im)))
      ↔ z ∈ stripFinsetPos T ∧ z.re = 1 / 2 ∧ Odd ((analyticOrderAt xi z).toNat) := by
  classical
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hmem, hre, hodd⟩
    refine ⟨hmem, hre, ?_⟩
    have hz : z = linePt z.im := Complex.ext (by rw [hre, linePt_re]) (by rw [linePt_im])
    rw [hz]
    exact (xiHorizontalMultiplicity_odd_iff z.im).mp hodd
  · rintro ⟨hmem, hre, hodd⟩
    refine ⟨hmem, hre, ?_⟩
    have hz : z = linePt z.im := Complex.ext (by rw [hre, linePt_re]) (by rw [linePt_im])
    refine (xiHorizontalMultiplicity_odd_iff z.im).mpr ?_
    rw [← hz]
    exact hodd

end RHTower

end
