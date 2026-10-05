import GaloisForLFunctions.RHTower.ChiRamanujanTransverseDefectGrid
import GaloisForLFunctions.RHTower.EstermannKloostermanSaving

/-!
# Full tangential profiles on signed transverse fibres

The zero fibre retains both coordinate axes and their intersection. Every
nonzero fibre is the weighted inverse curve. Exact two-variable finite
Fourier inversion identifies the full inverse-curve profile with its
Kloosterman pairing. The literal complete prime-square base source is
attached without replacing its tangential profile by a product test.
No growing physical cancellation estimate is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace
local instance (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩

private lemma sum_field (p : Nat.Primes) (f : ZMod (p : ℕ) → ℂ) :
    (∑ a, f a)=f 0+∑ u : (ZMod (p : ℕ))ˣ, f u := by
  rw [RHTower.sum_units_eq_sum_ite]
  calc
    _ = ∑ a : ZMod (p : ℕ),
        ((if a=0 then f 0 else 0)+(if a=0 then 0 else f a)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : a=0 <;> simp [h]
    _ = _ := by simp [Finset.sum_add_distrib]

def criticalProfileFibre (p : Nat.Primes) (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ)
    (d : ZMod (p : ℕ)) : ℂ :=
  ∑ a, ∑ b, if a*b=d then criticalDefectBase p a*criticalDefectBase p b*H a b else 0

def criticalProfileInverse (p : Nat.Primes) (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ)
    (d : ZMod (p : ℕ)) : ℂ :=
  ∑ u : (ZMod (p : ℕ))ˣ, H u (d*(u⁻¹ : (ZMod (p : ℕ))ˣ))

def criticalProfileAxes (p : Nat.Primes) (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) : ℂ :=
  (1-(p : ℂ)⁻¹)^2*H 0 0-
    (1-(p : ℂ)⁻¹)*(p : ℂ)⁻¹*
      ∑ u : (ZMod (p : ℕ))ˣ, (H u 0+H 0 u)

private lemma unit_fibre (p : Nat.Primes) (u : (ZMod (p : ℕ))ˣ)
    (d b : ZMod (p : ℕ)) : (u : ZMod (p : ℕ))*b=d ↔ b=d*(u⁻¹ : (ZMod (p : ℕ))ˣ) := by
  constructor
  · intro h
    have he := congrArg (fun x : ZMod (p : ℕ) => (u⁻¹ : (ZMod (p : ℕ))ˣ)*x) h
    rw [← mul_assoc,Units.inv_mul,one_mul] at he
    exact he.trans (mul_comm _ _)
  · intro h
    rw [h]
    calc
      _ = d*((u : ZMod (p : ℕ))*(u⁻¹ : (ZMod (p : ℕ))ˣ)) := by ring
      _ = d := by rw [Units.mul_inv,mul_one]

/-- Both axes and their intersection are retained in the zero defect fibre. -/
theorem criticalProfileFibre_zero (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) :
    criticalProfileFibre p H 0=criticalProfileAxes p H := by
  unfold criticalProfileFibre
  rw [sum_field p]
  simp only [zero_mul,if_true]
  rw [sum_field p]
  have hr (u : (ZMod (p : ℕ))ˣ) :
      (∑ b : ZMod (p : ℕ), if (u : ZMod (p : ℕ))*b=0 then
        criticalDefectBase p u*criticalDefectBase p b*H u b else 0) =
      -(p : ℂ)⁻¹*(1-(p : ℂ)⁻¹)*H u 0 := by
    simp [mul_eq_zero,Units.ne_zero,criticalDefectBase]
  simp_rw [hr]
  simp only [criticalDefectBase,ite_true,if_neg (Units.ne_zero _)]
  simp only [criticalProfileAxes,Finset.sum_add_distrib,← Finset.mul_sum]
  ring

private lemma fibre_nonzero (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) {d : ZMod (p : ℕ)} (hd : d ≠ 0) :
    criticalProfileFibre p H d=(p : ℂ)⁻¹^2*criticalProfileInverse p H d := by
  unfold criticalProfileFibre
  rw [sum_field p]
  simp only [zero_mul,if_neg (Ne.symm hd),Finset.sum_const_zero,zero_add]
  have hr (u : (ZMod (p : ℕ))ˣ) :
      (∑ b : ZMod (p : ℕ), if (u : ZMod (p : ℕ))*b=d then
        criticalDefectBase p u*criticalDefectBase p b*H u b else 0) =
      (p : ℂ)⁻¹^2*H u (d*(u⁻¹ : (ZMod (p : ℕ))ˣ)) := by
    simp_rw [unit_fibre]
    have hu : (u : ZMod (p : ℕ)) ≠ 0 := Units.ne_zero u
    have hv : d*(u⁻¹ : (ZMod (p : ℕ))ˣ) ≠ 0 := mul_ne_zero hd (Units.ne_zero (u⁻¹))
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,criticalDefectBase,
      if_neg hu,if_neg hv,zero_sub,neg_mul_neg,pow_two]
  simp_rw [hr]
  rw [← Finset.mul_sum]
  rfl

/-- Exact full-profile defect law, without a separability or cancellation premise. -/
theorem criticalProfileFibre_eq (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) (d : ZMod (p : ℕ)) :
    criticalProfileFibre p H d = if d=0 then criticalProfileAxes p H else
      (p : ℂ)⁻¹^2*criticalProfileInverse p H d := by
  by_cases hd : d=0
  · subst d
    simp only [if_true,criticalProfileFibre_zero]
  · rw [if_neg hd,fibre_nonzero p H hd]

/-- Full signed pairing with arbitrary tangential and defect profiles. -/
theorem criticalProfile_pairing (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) (Φ : ZMod (p : ℕ) → ℂ) :
    (∑ a, ∑ b, criticalDefectBase p a*criticalDefectBase p b*H a b*Φ (a*b)) =
      ∑ d, (if d=0 then criticalProfileAxes p H else
        (p : ℂ)⁻¹^2*criticalProfileInverse p H d)*Φ d := by
  symm
  simp_rw [← criticalProfileFibre_eq,criticalProfileFibre,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp [ite_mul]

def criticalProfileFourier (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) (m n : ZMod (p : ℕ)) : ℂ :=
  ZMod.dft (fun b => ZMod.dft (fun a => H a b) m) n

private lemma inversion (p : Nat.Primes) (f : ZMod (p : ℕ) → ℂ) (a : ZMod (p : ℕ)) :
    f a=(p : ℂ)⁻¹*∑ m, ZMod.stdAddChar (m*a)*ZMod.dft f m := by
  have he := congrFun ((ZMod.dft (N := (p : ℕ))).symm_apply_apply f) a
  simpa only [ZMod.invDFT_apply,smul_eq_mul] using he.symm

/-- Both tangential frequencies are retained, with exact finite Fourier normalization. -/
theorem criticalProfileFourier_inversion (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) (a b : ZMod (p : ℕ)) :
    H a b=(p : ℂ)⁻¹^2*∑ m, ∑ n,
      criticalProfileFourier p H m n*ZMod.stdAddChar (m*a+n*b) := by
  rw [inversion p (fun a => H a b) a]
  have he (m : ZMod (p : ℕ)) :
      ZMod.dft (fun a => H a b) m =
        (p : ℂ)⁻¹*∑ n, ZMod.stdAddChar (n*b)*criticalProfileFourier p H m n :=
    inversion p (fun b => ZMod.dft (fun a => H a b) m) b
  simp only [he,AddChar.map_add_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The full inverse fibre is the complete two-frequency Kloosterman pairing. -/
theorem criticalProfileInverse_kloosterman (p : Nat.Primes)
    (H : ZMod (p : ℕ) → ZMod (p : ℕ) → ℂ) (d : ZMod (p : ℕ)) :
    criticalProfileInverse p H d = (p : ℂ)⁻¹^2*∑ m, ∑ n,
      criticalProfileFourier p H m n*RHTower.Sieve.kloostermanSum (p : ℕ) m (n*d) := by
  unfold criticalProfileInverse
  simp_rw [criticalProfileFourier_inversion p H,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum]
  congr 1
  unfold RHTower.Sieve.kloostermanSum RHTower.Sieve.kloostermanPhase
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_assoc]

/-- Literal complete prime-square base source with its full two-coordinate test. -/
theorem criticalGridBase_profile_pairing (p : Nat.Primes)
    (H : Fin ((p : ℕ)^2) → Fin ((p : ℕ)^2) → ℂ) :
    (∑ k, ∑ l, (ramanujanGridBase p k : ℂ)*(ramanujanGridBase p l : ℂ)*H k l*
      ramanujanFourierPhase (p : ℕ)
        (((k.val : ℝ)/((p : ℕ)^2 : ℕ))*((l.val : ℝ)/((p : ℕ)^2 : ℕ)))) =
    ∑ d : ZMod (p : ℕ),
      (if d=0 then criticalProfileAxes p (fun a b => H (criticalDefectGridNode p a) (criticalDefectGridNode p b))
      else (p : ℂ)⁻¹^2*criticalProfileInverse p
        (fun a b => H (criticalDefectGridNode p a) (criticalDefectGridNode p b)) d)*ZMod.stdAddChar d := by
  simp_rw [mul_assoc,← Finset.mul_sum,criticalDefectGridBase_sum]
  simp_rw [Finset.mul_sum,← mul_assoc,criticalDefectGridNode_phase]
  exact criticalProfile_pairing p _ _

end RHTower.BAGTrace
