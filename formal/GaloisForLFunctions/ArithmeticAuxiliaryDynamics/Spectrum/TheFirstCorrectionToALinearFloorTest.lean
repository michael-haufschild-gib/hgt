import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.ResiduePrimitivesOfAFloorRow
import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel

/-!
# Linear tests of an integer floor row

The quadratic primitive has period mean Σ k c(k)/12. Its centered
primitive is an explicit periodic cubic. Hence the first correction
to testing the row against x on [0,1] is known at every common period.
One of the first two translates incurs at least one quarter of the
peak divided by the mesh length, at every such length.
-/

noncomputable section
open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
open _root_.HTGeometry
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

/-- Mean of the quadratic primitive of a balanced row. -/
def floorPrimitiveMean (c : ℕ →₀ ℤ) : ℝ := (∑ k ∈ c.support, (k:ℝ)*(c k:ℝ))/12

/-- Cubic periodic primitive after removing the quadratic primitive's mean. -/
def cubicFloorPrimitive (c : ℕ →₀ ℤ) (n : ℕ) : ℝ :=
  ∑ k ∈ c.support, -(c k:ℝ)*centeredModularSecondPrimitive k n

private theorem mean_from_letters {c : ℕ →₀ ℤ} (hc : c 0 = 0) (hb : IsBalanced c) :
    (∑ k ∈ c.support, (c k:ℝ)*centeredModularMeanMagnitude k) = floorPrimitiveMean c := by
  have ht (k : ℕ) (hk : k ∈ c.support) :
      (c k:ℝ)*centeredModularMeanMagnitude k = ((k:ℝ)*(c k:ℝ)-(c k:ℝ)/k)/12 := by
    have hk' : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (fun he => Finsupp.mem_support_iff.mp hk (he ▸ hc))
    unfold centeredModularMeanMagnitude
    field_simp
    ring
  rw [sum_congr rfl ht,←sum_div,sum_sub_distrib,show (∑ k ∈ c.support, (c k:ℝ)/k)=0 from hb,sub_zero]
  rfl

theorem cubic_floor_step {c : ℕ →₀ ℤ} (hc : c 0=0) (hb : IsBalanced c) (n : ℕ) :
    cubicFloorPrimitive c (n+1)-cubicFloorPrimitive c n =
      floorRowPrimitive c (n+1)-floorPrimitiveMean c := by
  rw [←mean_from_letters hc hb,cubicFloorPrimitive,cubicFloorPrimitive,floorRowPrimitive,
    ←sum_sub_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  have hk' : 0 < k := Nat.pos_of_ne_zero (fun he => Finsupp.mem_support_iff.mp hk (he ▸ hc))
  rw [←mul_sub,centeredModularSecondPrimitive_succ hk',
    show centeredModularPrimitive k (n+1) = -residuePrimitive k (n+1) by
      unfold centeredModularPrimitive residuePrimitive; ring]
  ring

/-- Exact affine moment for any translated interval, including its cubic
endpoint correction when the interval cuts through a period. -/
theorem affine_floor_window {c : ℕ →₀ ℤ} (hc : c 0=0) (hb : IsBalanced c) (n L : ℕ) :
    (∑ i ∈ range L, ((stepWeight c (n+i):ℝ)-(peak c:ℝ)/2)*i) =
      L*(floorRowPrimitive c (n+L)-floorPrimitiveMean c) -
        (cubicFloorPrimitive c (n+L)-cubicFloorPrimitive c n) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ,ih,floor_row_primitive_step hc hb,Nat.cast_succ,Nat.add_succ]
    linarith only [cubic_floor_step hc hb (n+L)]

/-- Error against the affine observable x at equally spaced mesh points
i/L, normalized by the length of the interval. -/
def affineFloorError (c : ℕ →₀ ℤ) (n L : ℕ) : ℝ :=
  (∑ i ∈ range L, ((stepWeight c (n+i):ℝ)-(peak c:ℝ)/2)*i)/(L:ℝ)^2

/-- Doubling the number of complete periods halves the error exactly. -/
theorem affine_floor_error_at_period {c : ℕ →₀ ℤ} (hc : c 0=0) (hb : IsBalanced c)
    (n : ℕ) {L : ℕ} (hL : 0 < L) (hd : ∀ k ∈ c.support, k ∣ L) :
    (L:ℝ)*affineFloorError c n L = floorRowPrimitive c n-floorPrimitiveMean c := by
  have hh (k : ℕ) (hk : k ∈ c.support) : (n+L)%k=n%k := by
    simp only [Nat.add_mod,Nat.mod_eq_zero_of_dvd (hd k hk),Nat.add_zero,Nat.mod_mod]
  have hp : floorRowPrimitive c (n+L) = floorRowPrimitive c n :=
    sum_congr rfl fun k hk => by simp only [residuePrimitive,hh k hk]
  have hq : cubicFloorPrimitive c (n+L) = cubicFloorPrimitive c n :=
    sum_congr rfl fun k hk => by simp only [centeredModularSecondPrimitive,hh k hk]
  rw [affineFloorError,affine_floor_window hc hb,hp,hq,sub_self,sub_zero]
  have hl : (L:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp

/-- For every producer one fixed translate, either zero or one, attains
the first-order error floor on every complete period. -/
theorem two_translates_force_affine_error (c : ℕ →₀ ℤ) (m B : ℕ) (hP : IsProducer c m B) :
    ∃ n ≤ 1, ∀ L : ℕ, 0 < L → (∀ k ∈ c.support, k ∣ L) →
      (peak c:ℝ)/4 ≤ (L:ℝ)*|affineFloorError c n L| := by
  let d (n : ℕ) := floorRowPrimitive c n-floorPrimitiveMean c
  have hs := floor_row_primitive_step hP.zero hP.balanced 0
  rw [stepWeight_zero,Int.cast_zero,zero_sub] at hs
  have hd : (peak c:ℝ)/2 = d 0-d 1 := by dsimp only [d]; linarith only [hs]
  have h : ∃ n ≤ 1, (peak c:ℝ)/4 ≤ |d n| := by
    rcases le_or_gt ((peak c:ℝ)/4) |d 0| with h | h
    · exact ⟨0,by omega,h⟩
    · exact ⟨1,le_rfl,by linarith only [hd,(le_abs_self _).trans (abs_sub (d 0) (d 1)),h]⟩
  obtain ⟨n,hn,H⟩ := h
  refine ⟨n,hn,fun L hL hdiv => ?_⟩
  simpa only [abs_mul,abs_of_nonneg (Nat.cast_nonneg L)] using
    H.trans_eq (congrArg abs (affine_floor_error_at_period hP.zero hP.balanced n hL hdiv)).symm

#print axioms cubic_floor_step
#print axioms affine_floor_error_at_period
#print axioms two_translates_force_affine_error

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
