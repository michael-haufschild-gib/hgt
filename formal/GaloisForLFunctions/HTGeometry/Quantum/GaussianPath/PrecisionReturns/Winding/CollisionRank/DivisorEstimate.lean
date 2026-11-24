import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.LogApproximation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.CollisionRank.ForestRatios
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Arc

/-! # Common divisors of simultaneous spectral windings -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
noncomputable section

private theorem numerator_error {D t R g₀ g₁ p₀ p₁ : ℝ}
    (hD : 0 < D) (hg : g₀ ≠ 0) (he : |t*g₁-D*p₁| ≤ R) (he₀ : |t*g₀-D*p₀| ≤ R)
    {A : ℝ} (hA : |g₁/g₀| ≤ A) :
    |p₀*(g₁/g₀)-p₁| ≤ (1+A)*R/D := by
  apply (le_div_iff₀ hD).mpr
  have hid : (p₀*(g₁/g₀)-p₁)*D=(t*g₁-D*p₁)-(g₁/g₀)*(t*g₀-D*p₀) := by
    field_simp [hg]; ring
  rw [show |p₀*(g₁/g₀)-p₁| * D = |(p₀*(g₁/g₀)-p₁)*D| by rw [abs_mul,abs_of_pos hD],hid]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  exact (add_le_add he (mul_le_mul hA he₀ (abs_nonneg _) (le_trans (abs_nonneg _) hA))).trans_eq (by ring)

/-- An extremal packet of n+1 colliding gap windings gives a joint
logarithmic bound on any common modulus, allowing different roots for
different leaves. The constant is independent of the date and modulus. -/
theorem forest_divisor_estimate {I : Type*} {n : ℕ} (leaf root : Fin (n+1) → I)
    (w : I → ℝ) (hg₀ : w (leaf 0)-w (root 0) ≠ 0)
    (hy : ¬ KleinbockMargulis.VWA (forestRatio leaf root w)) {η : ℝ} (hη : 0 < η) :
    let b := ((n:ℝ))⁻¹+η
    ∃ C : ℝ, ∀ t R : ℝ, 1 ≤ t → R ∈ Ioc (0:ℝ) 1 → R < t*|w (leaf 0)-w (root 0)| →
      ∀ a z, Anchored w t R a z → ∀ d : ℕ, 0 < d →
        (∀ i, (d:ℤ) ∣ z (leaf i)-z (root i)) →
          (1+b)*log (d:ℝ) ≤ C+log R+b*log t := by
  intro b
  let y := forestRatio leaf root w
  let g := fun i => w (leaf i)-w (root i)
  let A := ‖y‖
  have hA : 0 ≤ A := norm_nonneg _
  have hcoef : 0 < 1+A := by positivity
  have hbase : 0 < |g 0|+1 := by positivity
  have hb : 0 ≤ b := add_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hη.le
  obtain ⟨B,hB⟩ := integer_log_approximation hy hη
  refine ⟨B+log (1+A)+b*log (|g 0|+1),?_⟩
  intro t R ht hR hlate a z hz d hd hdiv
  choose p hp using hdiv
  have hD := Nat.cast_pos (α:=ℝ).mpr hd
  have ht₀ := zero_lt_one.trans_le ht
  have gap (i) : |t*g i-(d:ℝ)*(p i:ℝ)| ≤ R := by
    have he := congrArg (fun k : ℤ => (k:ℝ)) (hp i)
    push_cast at he
    change |t*(w (leaf i)-w (root i))-(d:ℝ)*(p i:ℝ)| ≤ R
    rw [←he]
    exact abs_le.mpr ⟨by linarith only [(hz (leaf i)).1,(hz (root i)).2],
      by linarith only [(hz (leaf i)).2,(hz (root i)).1]⟩
  have hp₀ : p 0 ≠ 0 := by
    intro h
    have hh := gap 0
    rw [h,Int.cast_zero,mul_zero,sub_zero,abs_mul,abs_of_pos ht₀] at hh
    exact hlate.not_ge hh
  have hq' : 0 < |(p 0:ℝ)| := abs_pos.mpr (by exact_mod_cast hp₀)
  have hq : |(p 0:ℝ)| ≤ (|g 0|+1)*t/d := by
    apply (le_div_iff₀ hD).mpr
    rw [show |(p 0:ℝ)| * (d:ℝ) = |(d:ℝ)*(p 0:ℝ)| by rw [abs_mul,abs_of_pos hD,mul_comm]]
    have hh := abs_sub_le ((d:ℝ)*(p 0:ℝ)) (t*g 0) 0
    rw [sub_zero,sub_zero,abs_sub_comm ((d:ℝ)*(p 0:ℝ)),abs_mul t,abs_of_pos ht₀] at hh
    linarith only [hh,gap 0,hR.2,ht]
  have hnorm (i : Fin n) : |g i.succ/g 0| ≤ A := norm_le_pi_norm y i
  have hhit (i : Fin n) : |(p 0:ℝ)*y i-(p i.succ:ℝ)| ≤ (1+A)*R/d :=
    numerator_error hD hg₀ (gap i.succ) (gap 0) (hnorm i)
  have hfit := hB (p 0) hp₀ (fun i => p i.succ) _ (div_pos (mul_pos hcoef hR.1) hD) hhit
  have hlog := log_le_log hq' hq
  rw [log_div (mul_pos hcoef hR.1).ne' hD.ne',log_mul hcoef.ne' hR.1.ne'] at hfit
  rw [log_div (mul_pos hbase ht₀).ne' hD.ne',log_mul hbase.ne' ht₀.ne'] at hlog
  linarith only [hfit,mul_le_mul_of_nonneg_left hlog hb]

#print axioms forest_divisor_estimate
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.CollisionRank
