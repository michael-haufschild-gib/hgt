import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Capped.Strip

/-! # Transfer coordinates for the two spectral edges of a three-prime sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped

open Finset

variable (S : Finset Nat.Primes) (hs : S.card = 3)

def species : Fin 3 ≃ S := (finCongr hs.symm).trans (enumeration S)

def e (i : Fin 3) := primeEnergy (species S hs i)

def lowerGap := e S hs 1 - e S hs 0

def upperGap := e S hs 2 - e S hs 1

def lowerEnergy (k l : ℕ) := ((k+l : ℕ) : ℝ)*e S hs 0 + k*e S hs 1

def upperEnergy (k l : ℕ) := ((k+l : ℕ) : ℝ)*e S hs 2 + k*e S hs 1

abbrev Sector (S : Finset Nat.Primes) (k l : ℕ) := State (fun _ : S => k+l) (k+l+k)

def lowerSpectrum (k l : ℕ) := Set.range (fun x : Sector S k l => energy (level x)-lowerEnergy S hs k l)

def upperSpectrum (k l : ℕ) := Set.range (fun x : Sector S k l => upperEnergy S hs k l-energy (level x))

private theorem sum_three {M : Type*} [AddCommMonoid M] (f : S → M) :
    ∑ i, f i = f (species S hs 0) + (f (species S hs 1) + f (species S hs 2)) := by
  rw [← Equiv.sum_comp (species S hs) f]
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rfl

variable {k l : ℕ}

private def occ (x : Sector S k l) (i : Fin 3) := count x (species S hs i)

private theorem occ_sum (x : Sector S k l) :
    occ S hs x 0 + (occ S hs x 1 + occ S hs x 2) = k+l+k :=
  (sum_three S hs (count x)).symm.trans (count_sum x)

private theorem energy_three (x : Sector S k l) : energy (level x) =
    (occ S hs x 0 : ℝ)*e S hs 0 + ((occ S hs x 1 : ℝ)*e S hs 1 + (occ S hs x 2 : ℝ)*e S hs 2) := by
  let y : Boson S (k+l+k) := ⟨fun i => ⟨count x i,Nat.lt_succ_of_le
    ((count_interval x i).2.trans (show min (k+l+k) (k+l) ≤ k+l+k from min_le_left _ _))⟩,count_sum x⟩
  rw [show level x = level y from rfl,energy_eq_read,read,sum_three S hs]
  rfl

private theorem realize (u v w : ℕ) (hu : u ≤ k+l) (hv : v ≤ k+l) (hw : w ≤ k+l)
    (hm : u+(v+w) = k+l+k) :
    ∃ x : Sector S k l, occ S hs x 0 = u ∧ occ S hs x 2 = w := by
  let f : Fin 3 → ℕ := ![u,v,w]
  have bound (i : Fin 3) : f i ≤ k+l := by fin_cases i <;> first | exact hu | exact hv | exact hw
  let x : Sector S k l := ⟨fun i => ⟨f ((species S hs).symm i),Nat.lt_succ_of_le (bound _)⟩,by
    change (∑ i, f ((species S hs).symm i)) = k+l+k
    rw [sum_three S hs]
    simp only [Equiv.symm_apply_apply]
    exact hm⟩
  refine ⟨x,?_,?_⟩ <;> simp only [occ,count,x,Equiv.symm_apply_apply] <;> rfl

private theorem transfer_allowed (x : Sector S k l) :
    Allowed k l (k+l-occ S hs x 0) (occ S hs x 2) := by
  have hu : occ S hs x 0 ≤ k+l := count_cap x _
  have hv : occ S hs x 1 ≤ k+l := count_cap x _
  have hw : occ S hs x 2 ≤ k+l := count_cap x _
  have sum := occ_sum S hs x
  unfold Allowed
  omega

private theorem transfer_exists (i j : ℕ) (h : Allowed k l i j) :
    ∃ x : Sector S k l, k+l-occ S hs x 0 = i ∧ occ S hs x 2 = j := by
  obtain ⟨hi,hj,hm,hn⟩ := h
  obtain ⟨x,hu,hw⟩ := realize S hs (k+l-i) (k+i-j) j (by omega) (by omega) hj (by omega)
  exact ⟨x,by rw [hu]; omega,hw⟩

private theorem flip_allowed {i j : ℕ} (h : Allowed k l i j) : Allowed l k (k+l-i) (k+l-j) := by
  unfold Allowed at *
  omega

private theorem displacements (x : Sector S k l) :
    energy (level x)-lowerEnergy S hs k l =
      height (lowerGap S hs) (upperGap S hs) (k+l-occ S hs x 0,occ S hs x 2) ∧
    upperEnergy S hs k l-energy (level x) =
      height (lowerGap S hs) (upperGap S hs) (occ S hs x 0,k+l-occ S hs x 2) := by
  have hu : occ S hs x 0 ≤ k+l := count_cap x _
  have hw : occ S hs x 2 ≤ k+l := count_cap x _
  have sm : (occ S hs x 0 : ℝ) + ((occ S hs x 1 : ℝ) + occ S hs x 2) = ((k+l : ℕ) : ℝ) + k := by
    exact_mod_cast occ_sum S hs x
  rw [energy_three S hs]
  simp only [height,lowerEnergy,upperEnergy,lowerGap,upperGap,Nat.cast_sub hu,Nat.cast_sub hw]
  constructor
  · linear_combination (e S hs 1)*sm
  · linear_combination -(e S hs 1)*sm

/-- The lower excitation set is exactly the arithmetic image of the lower feasibility strip. -/
theorem lowerSpectrum_eq (k l : ℕ) :
    lowerSpectrum S hs k l = band k l (lowerGap S hs) (upperGap S hs) := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨_,transfer_allowed S hs x,(displacements S hs x).1.symm⟩
  · rintro ⟨⟨i,j⟩,h,rfl⟩
    obtain ⟨x,hi,hj⟩ := transfer_exists S hs i j h
    exact ⟨x,(displacements S hs x).1.trans (by rw [hi,hj])⟩

/-- The upper excitation set exchanges filled and vacant sites of the middle mode. -/
theorem upperSpectrum_eq (k l : ℕ) :
    upperSpectrum S hs k l = band l k (lowerGap S hs) (upperGap S hs) := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    have h := flip_allowed (transfer_allowed S hs x)
    have hu : occ S hs x 0 ≤ k+l := count_cap x _
    rw [Nat.sub_sub_self hu] at h
    exact ⟨_,h,(displacements S hs x).2.symm⟩
  · rintro ⟨⟨i,j⟩,h,rfl⟩
    have fl := flip_allowed h
    rw [Nat.add_comm l k] at fl
    obtain ⟨x,hi,hj⟩ := transfer_exists S hs _ _ fl
    obtain ⟨hb,hc,_,_⟩ := h
    have hu : occ S hs x 0 ≤ k+l := count_cap x _
    have h₀ : occ S hs x 0 = i := by omega
    have h₂ : k+l-occ S hs x 2 = j := by omega
    exact ⟨x,(displacements S hs x).2.trans (by rw [h₀,h₂])⟩

#print axioms lowerSpectrum_eq
#print axioms upperSpectrum_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Capped
