import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.PolarizationAndPositivity
import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus

/-!
# One phase sweep of the reflected pulse Gram matrix

Phase averaging, as in Ghosh–Shuin's square-variation sign selection,
annihilates interference. Giving each pulse a distinct integer frequency
also preserves each individual cross term in a distinct Fourier mode
of the same scalar energy measurement. The marks below have cubic range.
The window can be the full reflected tail or any finite observation band.
-/

open MeasureTheory Complex Finset Set
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Integral phase marks for n channels. A difference modulo 2n
determines its signed index gap, whose square difference then determines
the sum of the two indices. -/
def pulsePhaseMark {n : ℕ} (i : Fin n) : ℤ := 2*(n:ℤ)*(i.val:ℤ)^2+i.val

private theorem phaseMark_delta {n : ℕ} {i j k l : Fin n}
    (h : pulsePhaseMark i-pulsePhaseMark j=pulsePhaseMark k-pulsePhaseMark l) :
    (i.val:ℤ)-j.val=(k.val:ℤ)-l.val ∧
      (i.val:ℤ)^2-(j.val:ℤ)^2=(k.val:ℤ)^2-(l.val:ℤ)^2 := by
  let e : ℤ := (i.val:ℤ)^2-(j.val:ℤ)^2-(k.val:ℤ)^2+(l.val:ℤ)^2
  let d : ℤ := (i.val:ℤ)-j.val-k.val+l.val
  have id : 2*(n:ℤ)*e+d=0 := by
    dsimp only [e,d]
    unfold pulsePhaseMark at h
    linarith only [h]
  have lo : -(2*(n:ℤ)) < d := by dsimp only [d]; have := j.isLt; have := k.isLt; omega
  have hi : d < 2*(n:ℤ) := by dsimp only [d]; have := i.isLt; have := l.isLt; omega
  have positive : 0≤2*(n:ℤ) := by positivity
  have hz : e=0 := by
    rcases lt_trichotomy e 0 with hn|he|hp
    · have le := mul_le_mul_of_nonneg_left (show e≤ -1 by omega) positive
      linarith only [le,id,hi]
    · exact he
    · have le := mul_le_mul_of_nonneg_left (show 1≤e by omega) positive
      linarith only [le,id,lo]
  have hd : d=0 := by simpa only [hz,mul_zero,zero_add] using id
  dsimp only [e] at hz
  dsimp only [d] at hd
  constructor <;> linarith only [hd,hz]

/-- Every nonzero pair frequency belongs to just one ordered pair. -/
theorem pulsePhaseMark_difference_unique {n : ℕ} {i j k l : Fin n} (hij : i≠j)
    (h : pulsePhaseMark i-pulsePhaseMark j=pulsePhaseMark k-pulsePhaseMark l) :
    i=k ∧ j=l := by
  obtain ⟨hd,hs⟩ := phaseMark_delta h
  have ne : (i.val:ℤ)-j.val≠0 := fun e => hij (Fin.ext (by exact_mod_cast sub_eq_zero.mp e))
  have hp : ((i.val:ℤ)-j.val)*((i.val:ℤ)+j.val-(k.val+l.val:ℤ))=0 := by
    linear_combination hs-((k.val:ℤ)+l.val)*hd
  have hsum := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left ne)
  constructor <;> apply Fin.ext <;> omega

private theorem phaseMark_injective {n : ℕ} : Function.Injective (@pulsePhaseMark n) := by
  intro i j h
  by_contra hn
  obtain ⟨_,eq⟩ := pulsePhaseMark_difference_unique hn
    (k:=i) (l:=i) (by rw [h,sub_self,sub_self])
  exact hn eq.symm

/-- Windowed Hermitian cross-energy between two reflected compact pulses. -/
def reflectedWindowGram (f g : CompactPulse) (W : Set ℝ) : ℂ :=
  ∫ t in W, pulseReflected f t * (starRingEnd ℂ) (pulseReflected g t)

def reflectedWindowEnergy (f : CompactPulse) (W : Set ℝ) : ℝ :=
  ∫ t in W, ‖pulseReflected f t‖^2

/-- Unit-period phase signal of integer frequency k. -/
def pulseTone (k : ℤ) (x : Unit → ℝ) := charLift (fun _ : Unit => k) x

/-- One-parameter mixture with one integer mark per input channel. -/
def markedPulse {n : ℕ} (f : Fin n → CompactPulse) (x : Unit → ℝ) : CompactPulse :=
  mixedPulse univ (fun i => pulseTone (pulsePhaseMark i) x) f

private theorem tone_difference (k l : ℤ) (x : Unit → ℝ) :
    pulseTone (k-l) x = pulseTone k x*(starRingEnd ℂ) (pulseTone l x) := by
  change charLift ((fun _ : Unit => k) + -(fun _ : Unit => l)) x = _
  rw [charLift_add_index,charLift_neg_index]

private theorem cast_norm_square (z : ℂ) : ((‖z‖^2:ℝ):ℂ)=z*(starRingEnd ℂ) z := by
  rw [Complex.mul_conj,Complex.sq_norm]

theorem reflectedWindowGram_self (f : CompactPulse) (W : Set ℝ) :
    reflectedWindowGram f f W=(reflectedWindowEnergy f W:ℂ) := by
  simp only [reflectedWindowGram,reflectedWindowEnergy,←cast_norm_square,integral_complex_ofReal]

/-- Complex form of the observed quadratic energy for arbitrary channel
amplitudes. Its coefficients are the physical cross-integrals. -/
theorem mixed_window_energy_gram {ι : Type*} [Fintype ι] (f : ι → CompactPulse) (W : Set ℝ)
    (c : ι → ℂ) :
    (reflectedWindowEnergy (mixedPulse univ c f) W:ℂ) =
      ∑ i, ∑ j, reflectedWindowGram (f i) (f j) W * (c i*(starRingEnd ℂ) (c j)) := by
  let t (i j : ι) := c i*(starRingEnd ℂ) (c j)
  let fgram (i j : ι) (T : ℝ) := pulseReflected (f i) T*(starRingEnd ℂ) (pulseReflected (f j) T)
  have hint i j : IntegrableOn (fun T => fgram i j T*t i j) W :=
    ((integrable_pulseReflected_mul_conj (f i) (f j)).mul_const _).integrableOn
  have point (T : ℝ) : ((‖pulseReflected (mixedPulse univ c f) T‖^2:ℝ):ℂ)=
      ∑ i, ∑ j, fgram i j T*t i j := by
    rw [cast_norm_square,pulseReflected_mixedPulse,map_sum,sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [map_mul]
    dsimp only [t,fgram]
    ring
  rw [reflectedWindowEnergy,←integral_complex_ofReal]
  simp_rw [point]
  rw [integral_finsetSum univ (fun i _ => integrable_finsetSum univ (fun j _ => hint i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum univ (fun j _ => hint i j)]
  exact sum_congr rfl fun j _ => integral_mul_const _ _

/-- The full scalar window energy, as a trigonometric polynomial in one
phase variable. Every nonzero frequency has one Hermitian coefficient. -/
theorem marked_window_energy_expansion {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ)
    (x : Unit → ℝ) :
    (reflectedWindowEnergy (markedPulse f x) W:ℂ) =
      ∑ i, ∑ j, reflectedWindowGram (f i) (f j) W * pulseTone (pulsePhaseMark i-pulsePhaseMark j) x := by
  simp only [markedPulse,mixed_window_energy_gram,tone_difference]

private theorem demodulate_energy {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ) (m : ℤ) :
    (∫ x in torusBox Unit, (reflectedWindowEnergy (markedPulse f x) W:ℂ)*
        (starRingEnd ℂ) (pulseTone m x)) =
      ∑ i, ∑ j, if pulsePhaseMark i-pulsePhaseMark j=m then reflectedWindowGram (f i) (f j) W else 0 := by
  let G (i j : Fin n) := reflectedWindowGram (f i) (f j) W
  let k (i j : Fin n) := pulsePhaseMark i-pulsePhaseMark j
  have hint i j : IntegrableOn
      (fun x => G i j*(pulseTone (k i j) x*(starRingEnd ℂ) (pulseTone m x))) (torusBox Unit) :=
    (integrableOn_box_charLift_mul_conj (fun _ : Unit => k i j) (fun _ : Unit => m)).const_mul _
  have point (x : Unit → ℝ) :
      (reflectedWindowEnergy (markedPulse f x) W:ℂ)*(starRingEnd ℂ) (pulseTone m x) =
        ∑ i, ∑ j, G i j*(pulseTone (k i j) x*(starRingEnd ℂ) (pulseTone m x)) := by
    simp only [marked_window_energy_expansion,sum_mul,G,k,mul_assoc]
  simp_rw [point]
  rw [integral_finsetSum univ (fun i _ => integrable_finsetSum univ (fun j _ => hint i j))]
  apply sum_congr rfl
  intro i _
  rw [integral_finsetSum univ (fun j _ => hint i j)]
  apply sum_congr rfl
  intro j _
  rw [integral_const_mul,show (∫ x in torusBox Unit, pulseTone (k i j) x*(starRingEnd ℂ) (pulseTone m x))=_
    from integral_box_charLift_mul_conj (fun _ : Unit => k i j) (fun _ : Unit => m)]
  by_cases eq : k i j=m
  · have he : (fun _ : Unit => k i j)=(fun _ : Unit => m) := funext fun _ => eq
    rw [if_pos he,mul_one,if_pos eq]
  · have ne : (fun _ : Unit => k i j)≠(fun _ : Unit => m) := fun e => eq (congrFun e ())
    simp only [if_neg ne,mul_zero,show pulsePhaseMark i-pulsePhaseMark j≠m from eq,if_false]

/-- The mean of the single phase sweep is exactly the incoherent energy. -/
theorem mean_marked_window_energy {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ) :
    (∫ x in torusBox Unit, reflectedWindowEnergy (markedPulse f x) W) =
      ∑ i, reflectedWindowEnergy (f i) W := by
  have mode := demodulate_energy f W 0
  simp only [pulseTone,show (fun _ : Unit => (0:ℤ))=0 from rfl,charLift_zero_index,map_one,
    mul_one,integral_complex_ofReal,sub_eq_zero,phaseMark_injective.eq_iff] at mode
  simpa only [Finset.sum_ite_eq,Finset.mem_univ,if_true,reflectedWindowGram_self,←Complex.ofReal_sum,
    Complex.ofReal_inj] using mode

/-- Fourier demodulation at an ordered difference recovers the full complex
cross-energy using only scalar energies of this single family. -/
theorem recover_reflected_window_gram {n : ℕ} (f : Fin n → CompactPulse) (W : Set ℝ)
    {i j : Fin n} (hij : i≠j) :
    (∫ x in torusBox Unit, (reflectedWindowEnergy (markedPulse f x) W:ℂ)*
      (starRingEnd ℂ) (pulseTone (pulsePhaseMark i-pulsePhaseMark j) x)) =
        reflectedWindowGram (f i) (f j) W := by
  rw [demodulate_energy]
  have eq (u v : Fin n) : pulsePhaseMark u-pulsePhaseMark v=pulsePhaseMark i-pulsePhaseMark j ↔
      u=i ∧ v=j := ⟨fun h => by obtain ⟨e,e'⟩ := pulsePhaseMark_difference_unique hij h.symm
                            exact ⟨e.symm,e'.symm⟩,
        fun ⟨e,e'⟩ => by rw [e,e']⟩
  simp only [eq,ite_and]
  classical
  simp [Finset.sum_ite_eq',Finset.sum_ite_eq]

/-- The same scan at a tail cut recovers each entry that appears in the
modular cumulative-decay problem. -/
theorem recover_tail_crossEnergy {n : ℕ} (f : Fin n → CompactPulse) (T : ℝ)
    {i j : Fin n} (hij : i≠j) :
    (∫ x in torusBox Unit, (tailEnergy (markedPulse f x) T:ℂ)*
      (starRingEnd ℂ) (pulseTone (pulsePhaseMark i-pulsePhaseMark j) x)) =
      tailCrossEnergy (f i) (f j) T :=
  recover_reflected_window_gram f (Ioi T) hij

end GaloisForLFunctions.BlackHoleRingdown
