import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.EdgeLimit
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.FirstParticle
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.ShortPackets

/-! # Exact resolution of the reflected peak test at large damping -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Real Filter Topology
open scoped ComplexConjugate

/-- In a bosonic sector of any positive degree, a simple first one-particle gap yields a
simple first many-particle gap of precisely the same size. -/
theorem boson_leakage {I : Type*} [Fintype I] [DecidableEq I] (n : ℕ) (e : I → ℝ)
    (l q : I) (hlq : e l < e q) (hrest : ∀ i, i ≠ l → i ≠ q → e q < e i) :
    Tendsto (fun t => exp (t*(e q-e l))*(1-largest (read e : Boson I (n+1) → ℝ) t)) atTop (𝓝 1) :=
  leakage_limit _ (pure (n+1) l) (firstExcitation n l q) (sub_pos.mpr hlq) (first_gap n l q e)
    (above_first_gap n e l q hlq hrest)

namespace ShortPacket

private theorem inc {A : ShortPacket} {i j : A.modes} (h : i.val.val < j.val.val) :
    primeEnergy i < primeEnergy j :=
  log_lt_log (Nat.cast_pos.mpr i.val.property.pos) (Nat.cast_lt.mpr h)

private theorem above_q (A : ShortPacket) (i : A.modes) (hl : i ≠ A.l) (hq : i ≠ A.q) :
    primeEnergy A.q < primeEnergy i := by
  rcases A.cases_mode i with h | h | h | h
  · exact (hl h).elim
  · exact (hq h).elim
  · subst i
    exact inc (lt_of_le_of_ne A.middle_le (fun he => hq (Subtype.ext (Subtype.ext he.symm))))
  · subst i; exact inc (A.middle_le.trans_lt A.high_lt)

private theorem below_r (A : ShortPacket) (i : A.modes) (hu : i ≠ A.u) (hr : i ≠ A.r) :
    primeEnergy i < primeEnergy A.r := by
  rcases A.cases_mode i with h | h | h | h
  · subst i; exact inc (A.low_lt.trans_le A.middle_le)
  · subst i
    exact inc (lt_of_le_of_ne A.middle_le (fun he => hr (Subtype.ext (Subtype.ext he))))
  · exact (hr h).elim
  · exact (hu h).elim

/-- The lower and upper adjacent prime ratios determine the two simple leakage exponents. -/
theorem edge_leakage (A : ShortPacket) (n : ℕ) :
    Tendsto (fun t => exp (t*(primeEnergy A.q-primeEnergy A.l))*
      (1-largest (read primeEnergy : Boson A.modes (n+1) → ℝ) t)) atTop (𝓝 1) ∧
    Tendsto (fun t => exp (t*(primeEnergy A.u-primeEnergy A.r))*
      (1-largest (read primeEnergy : Boson A.modes (n+1) → ℝ) (-t))) atTop (𝓝 1) := by
  constructor
  · exact boson_leakage n primeEnergy A.l A.q (inc A.low_lt) (above_q A)
  · have gap := inc (A := A) (i := A.r) (j := A.u) A.high_lt
    have upper := boson_leakage n (fun i : A.modes => -primeEnergy i) A.u A.r
      (neg_lt_neg gap) (fun i hu hr => neg_lt_neg (below_r A i hu hr))
    rw [read_neg_fun] at upper
    simpa only [largest_neg_energy, show -primeEnergy A.r - -primeEnergy A.u =
      primeEnergy A.u-primeEnergy A.r by ring] using upper

def edgeGap (A : ShortPacket) := min (primeEnergy A.q-primeEnergy A.l) (primeEnergy A.u-primeEnergy A.r)

theorem damping_limit (A : ShortPacket) (n : ℕ) :
    Tendsto (fun t => exp (t*A.edgeGap)*
      |largest (read primeEnergy : Boson A.modes (n+1) → ℝ) t -
       largest (read primeEnergy : Boson A.modes (n+1) → ℝ) (-t)|) atTop (𝓝 1) :=
  peak_gap_limit A.gaps_ne (A.edge_leakage n).1 (A.edge_leakage n).2

/-- The peak difference is asymptotic to exp(-|2 Re(s)-1| times the smaller edge gap),
along every approach to large absolute damping, independently of imaginary part. -/
theorem outgoing_resolution (A : ShortPacket) (n : ℕ) :
    Tendsto (fun s : ℂ => exp (|2*s.re-1| * A.edgeGap) *
      |measured A.modes (n+1) s-measured A.modes (n+1) (1-conj s)|)
      (comap (fun s : ℂ => |2*s.re-1|) atTop) (𝓝 1) := by
  have h := (A.damping_limit n).comp
    (tendsto_comap : Tendsto (fun s : ℂ => |2*s.re-1|) (comap _ atTop) atTop)
  refine h.congr' (Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply, measured_eq]
  have flip : 2*(1-conj s).re-1 = -(2*s.re-1) := by rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  rw [flip]
  by_cases hs : 0 ≤ 2*s.re-1
  · rw [abs_of_nonneg hs]
  · rw [abs_of_neg (lt_of_not_ge hs), neg_neg, abs_sub_comm]

#print axioms boson_leakage
#print axioms edge_leakage
#print axioms outgoing_resolution

end ShortPacket
end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
