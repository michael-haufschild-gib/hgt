import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.OnePhaseSweepOfTheReflectedPulseGram
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionFourierResolution

/-!
# A finite phase experiment for the complete modular receiver matrix

For an odd prime p, mark the p incoming pulses by the finite-field
parabola (i,i²). An ordered off-diagonal difference is unique. The
Fourier transform of scalar mixed energies therefore recovers every
complex cross-energy. Every row of settings has the same sum, so
p²−p+1 scalar mixtures and p−1 single-pulse readings suffice for the
full Hermitian matrix on any observation window.
-/

open Complex Finset MeasureTheory Set
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown

variable {p : ℕ} [Fact p.Prime]

/-- The two residue phases assigned to one incident pulse. -/
def pulseChirpMark (i : ZMod p) : Bool → ZMod p
  | false => i
  | true => i^2

/-- Linear and quadratic phase settings in the finite receiver experiment. -/
def pulseChirpGridPoint (u v : ZMod p) : Bool → ZMod p
  | false => u
  | true => v

/-- Residue frequency of an ordered pair of channels. -/
def pulseChirpDifference (q : ZMod p × ZMod p) : Bool → ZMod p :=
  pulseChirpMark q.1-pulseChirpMark q.2

/-- The linear coordinate gives the signed gap. Dividing the difference
of squares by that gap gives the sum, hence both endpoints. -/
private theorem pulseChirpDifference_unique (hp : 2 < p) {i j : ZMod p} (hij : i≠j)
    {q : ZMod p × ZMod p} (h : pulseChirpDifference q=pulseChirpDifference (i,j)) : q=(i,j) := by
  obtain ⟨k,l⟩ := q
  have hd : k-l=i-j := congrFun h false
  have hs : k^2-l^2=i^2-j^2 := congrFun h true
  rw [sq_sub_sq,sq_sub_sq,hd] at hs
  have he := mul_right_cancel₀ (sub_ne_zero.mpr hij) hs
  have htwo : (2:ZMod p)≠0 := fun h => hp.not_ge
    (Nat.le_of_dvd (by decide : 0<2) ((ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)))
  have hleft : 2*(k-i)=0 := by linear_combination he+hd
  have hk := sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left htwo)
  obtain rfl := hk
  exact Prod.ext rfl (by linear_combination -hd)

private theorem pulseChirpDifference_zero (i j : ZMod p) :
    pulseChirpDifference (i,j)=0 ↔ i=j := by
  constructor
  · intro h
    exact sub_eq_zero.mp (congrFun h false)
  · rintro rfl
    exact sub_self _

/-- Pulse formed by the quadratic character with the two control phases t. -/
def chirpPulse (f : ZMod p → CompactPulse) (t : Bool → ZMod p) : CompactPulse :=
  mixedPulse univ (fun i => torsionPhase p (pulseChirpMark i) t) f

private def coefficients (f : ZMod p → CompactPulse) (W : Set ℝ) (q : ZMod p × ZMod p) :=
  reflectedWindowGram (f q.1) (f q.2) W

private theorem chirp_expansion (f : ZMod p → CompactPulse) (W : Set ℝ) (t : Bool → ZMod p) :
    (reflectedWindowEnergy (chirpPulse f t) W:ℂ)=
      torsionPolynomial p univ pulseChirpDifference (coefficients f W) t := by
  simp only [chirpPulse,mixed_window_energy_gram,torsionPolynomial,Fintype.sum_prod_type,
    coefficients,pulseChirpDifference,torsionPhase_mul_conj]

/-- Exact complex cross-energy from the finite Fourier coefficient of
scalar window energies at one nonzero marked difference. -/
theorem chirp_recovers_cross_energy (hp : 2 < p) (f : ZMod p → CompactPulse) (W : Set ℝ)
    {i j : ZMod p} (hij : i≠j) :
    ∑ t : Bool → ZMod p, (reflectedWindowEnergy (chirpPulse f t) W:ℂ)*
        (starRingEnd ℂ) (torsionPhase p (pulseChirpDifference (i,j)) t) =
      (p:ℂ)^2*reflectedWindowGram (f i) (f j) W := by
  classical
  have fibre (q : ZMod p × ZMod p) :
      pulseChirpDifference q=pulseChirpDifference (i,j) ↔ q=(i,j) :=
    ⟨pulseChirpDifference_unique hp hij,fun e => congrArg pulseChirpDifference e⟩
  simp only [chirp_expansion,torsion_coefficient_recovery,residueCoefficient,Finset.sum_filter,
    fibre,Finset.sum_ite_eq',Finset.mem_univ,if_true,Fintype.card_bool,coefficients]

private theorem row_sum (a : Bool → ZMod p) (v : ZMod p) :
    ∑ u : ZMod p, torsionPhase p a (pulseChirpGridPoint u v)=
      ZMod.stdAddChar (v*a true)*(if a false=0 then (p:ℂ) else 0) := by
  simp only [torsionPhase,Fintype.prod_bool,pulseChirpGridPoint,←Finset.mul_sum]
  congr 1
  simpa only [ZMod.card] using AddChar.sum_mulShift (a false) (ZMod.isPrimitive_stdAddChar p)

/-- Every row integrates to p copies of the incoherent sum, independently
of the chosen quadratic phase. -/
theorem chirp_row_trace (f : ZMod p → CompactPulse) (W : Set ℝ) (v : ZMod p) :
    (∑ u : ZMod p, (reflectedWindowEnergy (chirpPulse f (pulseChirpGridPoint u v)) W:ℂ)) =
      (p:ℂ)*∑ i, (reflectedWindowEnergy (f i) W:ℂ) := by
  simp only [chirp_expansion,torsionPolynomial]
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,row_sum,Fintype.sum_prod_type,Finset.mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp [pulseChirpDifference,coefficients,pulseChirpMark,reflectedWindowGram_self,mul_comm]
  · intro j _ hji
    have hne : pulseChirpDifference (i,j) false≠0 := sub_ne_zero.mpr hji.symm
    simp only [if_neg hne,mul_zero]
  · exact fun h => (h (mem_univ i)).elim

/-- Readings retained from the p-by-p grid: one full row and every
nonzero linear frequency from the remaining rows. -/
def chirpSettings (p : ℕ) [NeZero p] : Finset (ZMod p × ZMod p) :=
  univ.filter fun q => q.1≠0 ∨ q.2=0

/-- The reduced array uses exactly one more setting than the number of
ordered pairs of distinct channels. Together with the single-channel
readings its cardinality is precisely p squared. -/
theorem chirp_settings_cardinality :
    (chirpSettings p).card=(p-1)*p+1 ∧ (chirpSettings p).card+(p-1)=p^2 := by
  classical
  have hp : 1≤p := (Fact.out : p.Prime).one_lt.le
  have form : chirpSettings p=insert (0,0) (((univ : Finset (ZMod p)).erase 0) ×ˢ univ) := by
    ext q
    obtain ⟨u,v⟩ := q
    simp only [chirpSettings,mem_filter,mem_univ,true_and,mem_insert,Prod.mk.injEq,
      mem_product,mem_erase,and_true]
    by_cases h : u=0 <;> simp [h]
  rw [form,card_insert_of_notMem (by simp),card_product,card_erase_of_mem (mem_univ 0),
    card_univ,ZMod.card]
  refine ⟨rfl,?_⟩
  calc (p-1)*p+1+(p-1) = (p-1)*p+p := by omega
       _ = (p-1+1)*p := by ring
       _ = p^2 := by rw [Nat.sub_add_cancel hp]; ring

private theorem recover_missing_readings (f g : ZMod p → CompactPulse) (W V : Set ℝ)
    (obs : ∀ u v : ZMod p, (u,v)∈chirpSettings p →
      reflectedWindowEnergy (chirpPulse f (pulseChirpGridPoint u v)) W=
        reflectedWindowEnergy (chirpPulse g (pulseChirpGridPoint u v)) V) :
    (∀ t, reflectedWindowEnergy (chirpPulse f t) W=reflectedWindowEnergy (chirpPulse g t) V) ∧
    (∑ i, (reflectedWindowEnergy (f i) W:ℂ))=∑ i, (reflectedWindowEnergy (g i) V:ℂ) := by
  classical
  let A (u v : ZMod p) : ℂ := reflectedWindowEnergy (chirpPulse f (pulseChirpGridPoint u v)) W
  let B (u v : ZMod p) : ℂ := reflectedWindowEnergy (chirpPulse g (pulseChirpGridPoint u v)) V
  have known {u v : ZMod p} (h : u≠0 ∨ v=0) : A u v=B u v :=
    congrArg Complex.ofReal (obs u v (Finset.mem_filter.mpr ⟨mem_univ _,h⟩))
  have total : (∑ u, A u 0) = ∑ u, B u 0 := sum_congr rfl (fun u _ => known (Or.inr rfl))
  change (∑ u, (reflectedWindowEnergy (chirpPulse f (pulseChirpGridPoint u 0)) W:ℂ))=
    ∑ u, (reflectedWindowEnergy (chirpPulse g (pulseChirpGridPoint u 0)) V:ℂ) at total
  rw [chirp_row_trace,chirp_row_trace] at total
  have diag := mul_left_cancel₀ (show (p:ℂ)≠0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) total
  refine ⟨fun t => ?_,diag⟩
  have all (v : ZMod p) : (∑ u, A u v)=∑ u, B u v := by
    change (∑ u, (reflectedWindowEnergy (chirpPulse f (pulseChirpGridPoint u v)) W:ℂ))=_
    exact (chirp_row_trace f W v).trans ((congrArg (fun z : ℂ => (p:ℂ)*z) diag).trans (chirp_row_trace g V v).symm)
  have zero (v : ZMod p) : A 0 v=B 0 v := by
    have tail : (∑ u ∈ univ.erase 0, A u v)=∑ u ∈ univ.erase 0, B u v :=
      sum_congr rfl (fun u hu => known (Or.inl (mem_erase.mp hu).1))
    have eq := all v
    rw [←sum_erase_add _ _ (mem_univ 0),←sum_erase_add _ _ (mem_univ 0),tail] at eq
    exact add_left_cancel eq
  have eta : pulseChirpGridPoint (t false) (t true)=t := funext fun b => by cases b <;> rfl
  rw [←eta]
  apply Complex.ofReal_injective
  change A (t false) (t true)=B (t false) (t true)
  rcases eq_or_ne (t false) 0 with h|h
  · rw [h]; exact zero (t true)
  · exact known (Or.inl h)

/-- The reduced quadratic settings and all but one single-pulse energies
determine the full complex receiver matrix. Both the incident pulses
and observation windows are allowed to differ between experiments. -/
theorem chirp_settings_determine_receiver_matrix (hp : 2 < p) (f g : ZMod p → CompactPulse)
    (W V : Set ℝ)
    (obs : ∀ u v : ZMod p, (u,v)∈chirpSettings p →
      reflectedWindowEnergy (chirpPulse f (pulseChirpGridPoint u v)) W=
        reflectedWindowEnergy (chirpPulse g (pulseChirpGridPoint u v)) V)
    (single : ∀ i : ZMod p, i≠0 → reflectedWindowEnergy (f i) W=reflectedWindowEnergy (g i) V) :
    ∀ i j, reflectedWindowGram (f i) (f j) W=reflectedWindowGram (g i) (g j) V := by
  classical
  obtain ⟨whole,total⟩ := recover_missing_readings f g W V obs
  intro i j
  rcases eq_or_ne i j with rfl|hne
  · rw [reflectedWindowGram_self,reflectedWindowGram_self]
    by_cases hi : i=0
    · subst i
      have tail : (∑ k ∈ univ.erase 0, (reflectedWindowEnergy (f k) W:ℂ))=
          ∑ k ∈ univ.erase 0, (reflectedWindowEnergy (g k) V:ℂ) :=
        sum_congr rfl fun k hk => congrArg Complex.ofReal (single k (mem_erase.mp hk).1)
      rw [←sum_erase_add _ _ (mem_univ 0),←sum_erase_add _ _ (mem_univ 0),tail] at total
      exact add_left_cancel total
    · exact congrArg Complex.ofReal (single i hi)
  · have eq := chirp_recovers_cross_energy hp f W hne
    simp_rw [whole] at eq
    rw [chirp_recovers_cross_energy hp g V hne] at eq
    exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) eq

#print axioms chirp_recovers_cross_energy
#print axioms chirp_settings_cardinality
#print axioms chirp_row_trace
#print axioms chirp_settings_determine_receiver_matrix
end GaloisForLFunctions.BlackHoleRingdown
