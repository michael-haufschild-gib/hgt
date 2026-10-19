import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgePhaseCode

/-!
# Exact fourth-data fibres of actual arithmetic edge signals

The existing Fourier readout identifies profiles with literal cutoff signals. Every arbitrary
competing real sieve signal with the prescribed fourth array is represented by one unique vector
in the explicit triangle/cycle code. Thus its ambiguity count is exactly two to the code nullity;
invisible coefficient tails are not counted as distinct signals.
-/

noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BezoutValuationIncidence
open AffineSieve
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- The existing exact Fourier readout makes each admitted coordinate a signal invariant. -/
theorem coordinate_of_signal_eq (N : ℕ) (c e : ℕ → ℝ)
    (hs : ∀ k, sieveSeq N c k = sieveSeq N e k) (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
    selbergMultiplesCoord N c q = selbergMultiplesCoord N e q := by
  have hc : residueSignal N (fun d => (c d : ℂ)) =
      residueSignal N (fun d => (e d : ℂ)) := by
    funext r
    have h := congrArg (fun x : ℝ => (x : ℂ)) (hs r.val)
    simpa only [← residueSignal_sieveSeq,ZMod.natCast_zmod_val] using h
  let r : ZMod N.factorial := (N.factorial/q : ℕ)
  have hr : addOrderOf r = q := frequency_order hq
  have hh := congrArg (fun f : ZMod N.factorial → ℂ => ZMod.dft f r) hc
  rw [dft_residueSignal,dft_residueSignal,hr,coordinate_ofReal,coordinate_ofReal] at hh
  have hn : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  exact Complex.ofReal_injective (mul_left_cancel₀ hn hh)

namespace ArithmeticEdges.Blocks
variable {V : Type*} [Fintype V] (D : Blocks V)

theorem weights_eq_of_profile_eq (n : ℕ) (a b : ℕ → ℝ)
    (h : ∀ q, D.profile a q = D.profile b q) : D.weights n a = D.weights n b :=
  congrArg (fun f => RHTower.pmRamanujanResidueCoeff f (D.cutoff n)) (funext h)

/-- Equality of actual cutoff signals is exactly equality of their canonical profiles. -/
theorem signal_weights_iff_profiles (n : ℕ) (a b : ℕ → ℝ) :
    (∀ k, sieveSeq (D.cutoff n) (D.weights n a) k =
      sieveSeq (D.cutoff n) (D.weights n b) k) ↔
        ∀ q, D.profile a q = D.profile b q := by
  constructor
  · intro h q
    by_cases hq : ∃ u v, u ≠ v ∧ q = D.order u v
    · obtain ⟨u,v,_,rfl⟩ := hq
      have hh := coordinate_of_signal_eq (D.cutoff n) (D.weights n a) (D.weights n b)
        h (D.order u v) (D.order_mem_cutoff n u v)
      simpa only [D.coordinate_weights] using hh
    · rw [D.profile_zero a q hq,D.profile_zero b q hq]
  · intro h k
    rw [D.weights_eq_of_profile_eq n a b h]

/-- The unique sign of a competing profile at each active order. -/
def phaseBetween (a b : ℕ → ℝ) : D.Phase a := by
  classical
  exact fun q => if D.profile b q = D.profile a q then 0 else 1

theorem twist_phaseBetween_of_squares (a b : ℕ → ℝ)
    (hs : ∀ q, (D.profile a q)^2 = (D.profile b q)^2) (q : ℕ) :
    D.twist a (D.phaseBetween a b) q = D.profile b q := by
  classical
  by_cases hq : q ∈ D.active a
  · rw [twist,D.phaseEval_mem a _ q hq]
    change BinaryPhase.sign (if D.profile b q = D.profile a q then 0 else 1) *
      D.profile a q = D.profile b q
    by_cases he : D.profile b q = D.profile a q
    · rw [if_pos he,BinaryPhase.sign_zero,one_mul,he]
    · have hh : D.profile b q = D.profile a q ∨ D.profile b q = -D.profile a q :=
        mul_self_eq_mul_self_iff.mp (by simpa only [pow_two] using (hs q).symm)
      rw [if_neg he,BinaryPhase.sign_one,hh.resolve_left he]
      ring
  · have ha : D.profile a q = 0 := by
      by_contra h
      exact hq ((D.mem_active_iff a q).mpr h)
    have hb : D.profile b q = 0 := by
      have h := hs q
      rw [ha] at h
      nlinarith only [h]
    simp [twist,ha,hb]

theorem profile_twist_phaseBetween (a b : ℕ → ℝ)
    (hs : ∀ q, (D.profile a q)^2 = (D.profile b q)^2) (q : ℕ) :
    D.profile (D.twist a (D.phaseBetween a b)) q = D.profile b q := by
  rw [D.profile_twist,D.twist_phaseBetween_of_squares a b hs]

theorem phaseBetween_mem_kernel_of_fourth (n : ℕ) (a b : ℕ → ℝ)
    (h : ∀ v : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
      translatedMoment (D.cutoff n) (D.weights n b) v) :
    D.phaseBetween a b ∈ LinearMap.ker (D.phaseMap a) := by
  have hs (q : ℕ) : (D.profile a q)^2 = (D.profile b q)^2 := by
    simpa only [D.coordinate_weights] using
      coordinate_squares_of_fourth_moments (D.cutoff n) (D.weights n a) (D.weights n b) h q
  apply (D.fourth_twist_iff_kernel n a _).mp
  have hw := D.weights_eq_of_profile_eq n (D.twist a (D.phaseBetween a b)) b
    (D.profile_twist_phaseBetween a b hs)
  intro v
  rw [hw]
  exact h v

/-- Distinct literal signals with the prescribed fourth array; competitors are arbitrary weights. -/
def FourthSignalFibre (n : ℕ) (a : ℕ → ℝ) :=
  {s : ℕ → ℝ // ∃ e : ℕ → ℝ, s = sieveSeq (D.cutoff n) e ∧
    ∀ v : Fin 4 → ℕ, translatedMoment (D.cutoff n) (D.weights n a) v =
      translatedMoment (D.cutoff n) e v}

def phaseToFourthSignal (n : ℕ) (a : ℕ → ℝ)
    (x : LinearMap.ker (D.phaseMap a)) : D.FourthSignalFibre n a :=
  ⟨sieveSeq (D.cutoff n) (D.weights n (D.twist a x.val)),
    ⟨D.weights n (D.twist a x.val),rfl,(D.fourth_twist_iff_kernel n a x.val).mpr x.property⟩⟩

theorem phaseToFourthSignal_injective (n : ℕ) (a : ℕ → ℝ) :
    Function.Injective (D.phaseToFourthSignal n a) := by
  intro x y h
  have hh := congrArg (fun s : D.FourthSignalFibre n a => s.val) h
  change sieveSeq (D.cutoff n) (D.weights n (D.twist a x.val)) =
    sieveSeq (D.cutoff n) (D.weights n (D.twist a y.val)) at hh
  have hp := (D.signal_weights_iff_profiles n (D.twist a x.val) (D.twist a y.val)).mp
    (fun k => congrFun hh k)
  apply Subtype.ext
  apply D.twist_injective a
  funext q
  simpa only [D.profile_twist] using hp q

theorem phaseToFourthSignal_surjective (n : ℕ) (a : ℕ → ℝ) :
    Function.Surjective (D.phaseToFourthSignal n a) := by
  intro s
  obtain ⟨e,hs,he⟩ := s.property
  have hsupport := ((D.fourth_weights_iff n a e).mp he).1
  let b := selbergMultiplesCoord (D.cutoff n) e
  have hsig (k : ℕ) : sieveSeq (D.cutoff n) e k =
      sieveSeq (D.cutoff n) (D.weights n b) k := D.signal_realization n e hsupport k
  have hb (v : Fin 4 → ℕ) : translatedMoment (D.cutoff n) (D.weights n a) v =
      translatedMoment (D.cutoff n) (D.weights n b) v := by
    simpa only [translatedMoment,hsig] using he v
  have hsq (q : ℕ) : (D.profile a q)^2 = (D.profile b q)^2 := by
    simpa only [D.coordinate_weights] using
      coordinate_squares_of_fourth_moments (D.cutoff n) (D.weights n a) (D.weights n b) hb q
  refine ⟨⟨D.phaseBetween a b,D.phaseBetween_mem_kernel_of_fourth n a b hb⟩,?_⟩
  apply Subtype.ext
  change sieveSeq (D.cutoff n) (D.weights n (D.twist a (D.phaseBetween a b))) = s.val
  funext k
  rw [D.weights_eq_of_profile_eq n (D.twist a (D.phaseBetween a b)) b
    (D.profile_twist_phaseBetween a b hsq)]
  exact (hsig k).symm.trans (congrFun hs k).symm

/-- Every arbitrary competing signal is represented by exactly one code vector. -/
def phaseFibreEquiv (n : ℕ) (a : ℕ → ℝ) :
    LinearMap.ker (D.phaseMap a) ≃ D.FourthSignalFibre n a :=
  Equiv.ofBijective (D.phaseToFourthSignal n a)
    ⟨D.phaseToFourthSignal_injective n a,D.phaseToFourthSignal_surjective n a⟩

/-- Exact ambiguity count for distinct actual cutoff signals, including empty support. -/
theorem fourth_signal_fibre_card (n : ℕ) (a : ℕ → ℝ) :
    Nat.card (D.FourthSignalFibre n a) = 2^((D.active a).card-D.phaseRank a) :=
  (Nat.card_congr (D.phaseFibreEquiv n a)).symm.trans (D.phase_kernel_card a)

end ArithmeticEdges.Blocks
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
