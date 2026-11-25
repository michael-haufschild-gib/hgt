import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Packets

/-! # Energy and exponential probes on the newly admitted finite prime packet -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

abbrev initial (c : ℝ) (h : Ioi (0:ℝ)) := Window.packet (primeCut c h)

abbrev added (c d : ℝ) (h : Ioi (0:ℝ)) := initial d h\initial c h

theorem initial_subset {c d : ℝ} (hcd : c ≤ d) (h : Ioi (0:ℝ)) : initial c h ⊆ initial d h := by
  intro p hp
  apply Sieve.mem_primeSubtypeLE.mpr
  refine (Sieve.mem_primeSubtypeLE.mp hp).trans (Nat.floor_mono (Real.exp_le_exp.mpr ?_))
  exact div_le_div_of_nonneg_right hcd h.property.le

def packetEnergy (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) (x : SquarefreeBitConfig S) :=
  h.val*finiteSquarefreeHamiltonian S x

def packetLaw (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) :=
  observed S (1+h.val) (packetEnergy S h)

def packetMoment (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) (z : ℂ) :=
  ∑ x, (finiteSquarefreeBornWeight S (1+h.val) x:ℂ)*Complex.exp (z*(packetEnergy S h x:ℂ))

theorem packet_charFun (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) (t : ℝ) :
    charFun (packetLaw S h : Measure ℝ) t = packetMoment S h ((t:ℂ)*Complex.I) := by
  change charFun (finiteAtomicObserverSpectrum _ _) t = _
  rw [charFun_finiteAtomicObserverSpectrum _ _ (fun x => (weight_pos S _ x).le),packetMoment]
  exact Finset.sum_congr rfl fun x _ => by rw [Complex.ofReal_mul,mul_right_comm (t:ℂ)]

/-- The finite Born measurement on the initial packet is the original conditioned gas. -/
theorem initial_moment (c : ℝ) (h : Ioi (0:ℝ)) (z : ℂ) :
    packetMoment (initial c h) h z = momentProbe c h 0 z := by
  have hs : 1+(h.val:ℂ) = ((1+h.val:ℝ):ℂ) := by push_cast; rfl
  rw [transform_partition,hs,Window.partition_real,← Window.partition_trace,Finset.sum_div,packetMoment]
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteSquarefreeBornWeight_eq,Complex.ofReal_div,Complex.ofReal_exp,div_mul_eq_mul_div,← Complex.exp_add]
  apply congrArg (fun u : ℂ => Complex.exp u/(finiteSquarefreePartition (initial c h) (1+h.val):ℂ))
  unfold packetEnergy
  push_cast
  ring

theorem initial_law (c : ℝ) (h : Ioi (0:ℝ)) :
    packetLaw (initial c h) h = conditionalLaw c h := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  rw [packet_charFun,initial_moment,charFun_conditionalLaw]

theorem packetMoment_split {A B : Finset Nat.Primes} (hAB : A ⊆ B) (h : Ioi (0:ℝ)) (z : ℂ) :
    packetMoment B h z = packetMoment A h z*packetMoment (B\A) h z := by
  let w (S : Finset Nat.Primes) (x : SquarefreeBitConfig S) :=
    (finiteSquarefreeBornWeight S (1+h.val) x:ℂ)*Complex.exp (z*(packetEnergy S h x:ℂ))
  let f (y : SquarefreeBitConfig A × SquarefreeBitConfig (B\A)) := w A y.1*w (B\A) y.2
  have hw (x : SquarefreeBitConfig B) : w B x = f (splitBits hAB x) := by
    have he : (packetEnergy B h x:ℂ) = (packetEnergy A h (splitBits hAB x).1:ℂ)+
        (packetEnergy (B\A) h (splitBits hAB x).2:ℂ) := by
      simp only [packetEnergy,energy_split hAB x,mul_add,Complex.ofReal_add]
    dsimp only [w,f]
    rw [weight_split hAB,Complex.ofReal_mul,he,mul_add,Complex.exp_add]
    ring
  change (∑ x, w B x) = (∑ x, w A x)*(∑ y, w (B\A) y)
  rw [Finset.sum_congr rfl (fun x _ => hw x),(splitBits hAB).sum_comp f,Fintype.sum_prod_type,Finset.sum_mul_sum]

/-- The actual restriction of the high-cutoff vector to its two energy readings. -/
def jointEnergyLaw {c d : ℝ} (hcd : c ≤ d) (h : Ioi (0:ℝ)) :=
  observed (initial d h) (1+h.val) (fun x =>
    let y := splitBits (initial_subset hcd h) x
    (packetEnergy (initial c h) h y.1,packetEnergy (added c d h) h y.2))

theorem joint_exact_product {c d : ℝ} (hcd : c ≤ d) (h : Ioi (0:ℝ)) :
    jointEnergyLaw hcd h = (conditionalLaw c h).prod (packetLaw (added c d h) h) := by
  rw [← initial_law]
  exact observed_split (initial_subset hcd h) _ _ _

theorem finite_factor {c d : ℝ} (hcd : c ≤ d) (h : Ioi (0:ℝ)) (z : ℂ) :
    momentProbe d h 0 z = momentProbe c h 0 z*packetMoment (added c d h) h z := by
  rw [← initial_moment,← initial_moment]
  exact packetMoment_split (initial_subset hcd h) h z

#print axioms initial_subset
#print axioms packet_charFun
#print axioms initial_moment
#print axioms initial_law
#print axioms packetMoment_split
#print axioms joint_exact_product
#print axioms finite_factor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
