import GaloisForLFunctions.RHTower.PrimeCoShiftKernelProjection
import GaloisForLFunctions.RHTower.PrimeCoShiftRowGraph
import GaloisForLFunctions.HTGeometry.CommutingProjectionIntersectionEnergy

/-!
# The uniform orthogonal spectral gap of the all-prime co-shift row

For `Re s = σ > 1/2` the all-prime row `R_s x = ((V_p^* - p^{-s})x)_p` satisfies

```
‖R_s x‖² ≥ (1 - 2^{-σ})² ‖x - P_s x‖²                                   (1)
```

for every `x` in its domain, where `P_s` is the orthogonal projection onto the arithmetic ground
line `L_s = ℂ Ψ_s`.

Three inputs combine.  Each single-prime operator is bounded below by `1 - p^{-σ} ≥ 1 - 2^{-σ}` on
the orthogonal complement of its kernel, because its adjoint `V_p - conj(p^{-s})` is bounded below
by that constant.  The one-prime kernel projections commute, because the prime isometries doubly
commute.  And for a commuting family the defect energy of the intersection is at most the sum of
the individual defect energies.  The intersection is `L_s` by the common eigenline theorem.
-/

open scoped ENNReal NNReal InnerProductSpace
open RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.PrimeCoShift

noncomputable section

variable {s : ℂ}

/-- The scalar attached to the prime `p`. -/
def primeScalar (s : ℂ) (p : Nat.Primes) : ℂ := ((p : ℕ) : ℂ) ^ (-s)

theorem rowOp_eq_Top (s : ℂ) (p : Nat.Primes) :
    rowOp s p = Top (primePNat p) (primeScalar s p) := rfl

theorem norm_primeScalar (s : ℂ) (p : Nat.Primes) :
    ‖primeScalar s p‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [primeScalar, Complex.norm_natCast_cpow_of_pos p.property.pos]
  simp

theorem two_rpow_le (hs : 0 < s.re) (p : Nat.Primes) :
    ((p : ℕ) : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hbase : (2 : ℝ) ^ s.re ≤ ((p : ℕ) : ℝ) ^ s.re :=
    Real.rpow_le_rpow (by norm_num) hp2 hs.le
  have hposl : (0 : ℝ) < (2 : ℝ) ^ s.re := Real.rpow_pos_of_pos h2pos _
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by positivity)]
  exact inv_anti₀ hposl hbase

theorem two_rpow_lt_one {σ : ℝ} (hσ : 0 < σ) : (2 : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem norm_primeScalar_lt_one (hs : 0 < s.re) (p : Nat.Primes) :
    ‖primeScalar s p‖ < 1 := by
  rw [norm_primeScalar]
  exact lt_of_le_of_lt (two_rpow_le hs p) (two_rpow_lt_one hs)

/-- The one-prime kernel projection attached to `s` and `p`. -/
def rowProjection (s : ℂ) (hs : 0 < s.re) (p : Nat.Primes) : H →L[ℂ] H :=
  Pop (primePNat p) (norm_primeScalar_lt_one hs p)

theorem starProjection_rowKer (hs : 0 < s.re) (p : Nat.Primes) (x : H) :
    (LinearMap.ker (rowOp s p : H →ₗ[ℂ] H)).starProjection x = rowProjection s hs p x := by
  rw [rowOp_eq_Top]
  exact starProjection_ker_Top _ _ x

/-- **The one-prime gap, uniform in the prime.** -/
theorem gap_one_prime (hs : 0 < s.re) (p : Nat.Primes) (x : H) :
    (1 - (2 : ℝ) ^ (-s.re))
        * ‖x - (LinearMap.ker (rowOp s p : H →ₗ[ℂ] H)).starProjection x‖
      ≤ ‖rowOp s p x‖ := by
  have hbase := norm_Top_ge_norm_sub_Pop (primePNat p) (norm_primeScalar_lt_one hs p) x
  rw [starProjection_rowKer hs p x, rowProjection, rowOp_eq_Top]
  refine le_trans ?_ hbase
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h := two_rpow_le hs p
  rw [norm_primeScalar]
  linarith

/-! ### The one-prime kernels -/

/-- The kernel of the `p`-th row operator. -/
def rowKer (s : ℂ) (p : Nat.Primes) : Submodule ℂ H := LinearMap.ker (rowOp s p : H →ₗ[ℂ] H)

theorem eigenSubmodule_eq_iInf (s : ℂ) : eigenSubmodule s = ⨅ p : Nat.Primes, rowKer s p := rfl

theorem isClosed_rowKer (s : ℂ) (p : Nat.Primes) :
    IsClosed ((rowKer s p : Submodule ℂ H) : Set H) := (rowOp s p).isClosed_ker

theorem isClosed_finsetInf_rowKer (s : ℂ) (F : Finset Nat.Primes) :
    IsClosed (((F.inf (rowKer s)) : Submodule ℂ H) : Set H) := by
  classical
  induction F using Finset.induction with
  | empty =>
      have h : (∅ : Finset Nat.Primes).inf (rowKer s) = ⊤ := Finset.inf_empty
      rw [h]
      simpa using isClosed_univ
  | @insert a t _ ih =>
      have h : (insert a t).inf (rowKer s) = rowKer s a ⊓ t.inf (rowKer s) := Finset.inf_insert
      rw [h]
      have hcoe : ((rowKer s a ⊓ t.inf (rowKer s) : Submodule ℂ H) : Set H)
          = ((rowKer s a : Submodule ℂ H) : Set H)
            ∩ ((t.inf (rowKer s) : Submodule ℂ H) : Set H) := rfl
      rw [hcoe]
      exact (isClosed_rowKer s a).inter ih

theorem isClosed_iInf_rowKer (s : ℂ) :
    IsClosed (((⨅ p : Nat.Primes, rowKer s p) : Submodule ℂ H) : Set H) := by
  have hcoe : (((⨅ p : Nat.Primes, rowKer s p) : Submodule ℂ H) : Set H)
      = ⋂ p : Nat.Primes, ((rowKer s p : Submodule ℂ H) : Set H) := by
    ext y
    simp [Submodule.mem_iInf]
  rw [hcoe]
  exact isClosed_iInter fun p => isClosed_rowKer s p

instance rowKer_hasOrthogonalProjection (s : ℂ) (p : Nat.Primes) :
    (rowKer s p).HasOrthogonalProjection :=
  hasOrthogonalProjection_of_isClosed (isClosed_rowKer s p)

instance rowKerFinsetInf_hasOrthogonalProjection (s : ℂ) (F : Finset Nat.Primes) :
    ((F.inf (rowKer s)) : Submodule ℂ H).HasOrthogonalProjection :=
  hasOrthogonalProjection_of_isClosed (isClosed_finsetInf_rowKer s F)

instance iInf_rowKer_hasOrthogonalProjection (s : ℂ) :
    ((⨅ p : Nat.Primes, rowKer s p) : Submodule ℂ H).HasOrthogonalProjection :=
  hasOrthogonalProjection_of_isClosed (isClosed_iInf_rowKer s)

instance eigenSubmodule_hasOrthogonalProjection (s : ℂ) :
    (eigenSubmodule s).HasOrthogonalProjection := by
  rw [eigenSubmodule_eq_iInf]
  infer_instance

/-! ### Commuting one-prime projections -/

theorem commute_rowProjection (hs : 0 < s.re) (p q : Nat.Primes) :
    Commute (rowProjection s hs p) (rowProjection s hs q) := by
  rcases eq_or_ne p q with rfl | hne
  · exact Commute.refl _
  · refine commute_Pop_Pop _ _ ?_
    have hpq : (p : ℕ) ≠ (q : ℕ) := fun h => hne (Subtype.ext h)
    exact (Nat.coprime_primes p.property q.property).mpr hpq

theorem gap_one_prime' (hs : 0 < s.re) (p : Nat.Primes) (x : H) :
    (1 - (2 : ℝ) ^ (-s.re)) * ‖x - (rowKer s p).starProjection x‖ ≤ ‖rowOp s p x‖ :=
  gap_one_prime hs p x

theorem starProjection_rowKer_eq (hs : 0 < s.re) (p : Nat.Primes) (x : H) :
    (rowKer s p).starProjection x = rowProjection s hs p x :=
  starProjection_rowKer hs p x

theorem starProjection_rowKer_commute (hs : 0 < s.re) (p q : Nat.Primes) (y : H) :
    (rowKer s p).starProjection ((rowKer s q).starProjection y)
      = (rowKer s q).starProjection ((rowKer s p).starProjection y) := by
  have h := congrArg (fun T : H →L[ℂ] H => T y) (commute_rowProjection hs p q)
  simp only [ContinuousLinearMap.mul_apply] at h
  rw [starProjection_rowKer_eq hs q y, starProjection_rowKer_eq hs p y,
    starProjection_rowKer_eq hs p, starProjection_rowKer_eq hs q]
  exact h

/-! ### The global gap -/

/-- **The uniform orthogonal spectral gap of the all-prime row.** -/
theorem prime_row_spectral_gap (hs : 1 / 2 < s.re) {x : H} (hx : rowEnergy s x ≠ ⊤) :
    (1 - (2 : ℝ) ^ (-s.re)) ^ 2 * ‖x - (eigenSubmodule s).starProjection x‖ ^ 2
      ≤ ∑' p : Nat.Primes, ‖rowOp s p x‖ ^ 2 := by
  classical
  have hspos : 0 < s.re := by linarith
  set c : ℝ := 1 - (2 : ℝ) ^ (-s.re) with hcdef
  have hc : 0 < c := by
    have := two_rpow_lt_one hspos
    rw [hcdef]; linarith
  have hsummable : Summable fun p : Nat.Primes => ‖rowOp s p x‖ ^ 2 := rowEnergy_summable hx
  set R : ℝ := ∑' p : Nat.Primes, ‖rowOp s p x‖ ^ 2 with hRdef
  have hRnonneg : 0 ≤ R := tsum_nonneg fun p => sq_nonneg _
  have hF : ∀ F : Finset Nat.Primes,
      ∑ p ∈ F, ‖x - (rowKer s p).starProjection x‖ ^ 2 ≤ R / c ^ 2 := by
    intro F
    have hterm : ∀ p ∈ F,
        ‖x - (rowKer s p).starProjection x‖ ^ 2 ≤ (c ^ 2)⁻¹ * ‖rowOp s p x‖ ^ 2 := by
      intro p _
      have h := gap_one_prime' hspos p x
      rw [← hcdef] at h
      have hcA : (0 : ℝ) ≤ c * ‖x - (rowKer s p).starProjection x‖ := by positivity
      have h2 := mul_self_le_mul_self hcA h
      have hsq : c ^ 2 * ‖x - (rowKer s p).starProjection x‖ ^ 2 ≤ ‖rowOp s p x‖ ^ 2 := by
        calc c ^ 2 * ‖x - (rowKer s p).starProjection x‖ ^ 2
            = (c * ‖x - (rowKer s p).starProjection x‖)
              * (c * ‖x - (rowKer s p).starProjection x‖) := by ring
          _ ≤ ‖rowOp s p x‖ * ‖rowOp s p x‖ := h2
          _ = ‖rowOp s p x‖ ^ 2 := by ring
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    calc ∑ p ∈ F, ‖x - (rowKer s p).starProjection x‖ ^ 2
        ≤ ∑ p ∈ F, (c ^ 2)⁻¹ * ‖rowOp s p x‖ ^ 2 := Finset.sum_le_sum hterm
      _ = (c ^ 2)⁻¹ * ∑ p ∈ F, ‖rowOp s p x‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (c ^ 2)⁻¹ * R := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hsummable.sum_le_tsum F (fun p _ => sq_nonneg _)
      _ = R / c ^ 2 := by rw [inv_mul_eq_div]
  have habs := norm_sub_starProjection_iInf_sq_le (M := rowKer s)
    (starProjection_rowKer_commute hspos) (C := R / c ^ 2) x hF
  have heq : (⨅ p : Nat.Primes, rowKer s p).starProjection x
      = (eigenSubmodule s).starProjection x :=
    starProjection_congr (eigenSubmodule_eq_iInf s).symm x
  rw [heq] at habs
  have hfinal : c ^ 2 * ‖x - (eigenSubmodule s).starProjection x‖ ^ 2 ≤ c ^ 2 * (R / c ^ 2) :=
    mul_le_mul_of_nonneg_left habs (by positivity)
  rw [mul_div_cancel₀ _ (by positivity : (c : ℝ) ^ 2 ≠ 0)] at hfinal
  exact hfinal

/-- **Compact uniformity.**  The gap constant depends only on a lower bound for `Re s`. -/
theorem prime_row_spectral_gap_uniform {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) (hs : σ₀ ≤ s.re)
    {x : H} (hx : rowEnergy s x ≠ ⊤) :
    (1 - (2 : ℝ) ^ (-σ₀)) ^ 2 * ‖x - (eigenSubmodule s).starProjection x‖ ^ 2
      ≤ ∑' p : Nat.Primes, ‖rowOp s p x‖ ^ 2 := by
  have hs' : 1 / 2 < s.re := lt_of_lt_of_le hσ₀ hs
  have hmain := prime_row_spectral_gap hs' hx
  have hmono : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-σ₀) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h0 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-σ₀) := by
    have := two_rpow_lt_one (by linarith : (0:ℝ) < σ₀)
    linarith
  have hle : (1 - (2 : ℝ) ^ (-σ₀)) ^ 2 ≤ (1 - (2 : ℝ) ^ (-s.re)) ^ 2 := by
    have h1 : 1 - (2 : ℝ) ^ (-σ₀) ≤ 1 - (2 : ℝ) ^ (-s.re) := by linarith
    exact pow_le_pow_left₀ h0.le h1 2
  calc (1 - (2 : ℝ) ^ (-σ₀)) ^ 2 * ‖x - (eigenSubmodule s).starProjection x‖ ^ 2
      ≤ (1 - (2 : ℝ) ^ (-s.re)) ^ 2 * ‖x - (eigenSubmodule s).starProjection x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ ≤ ∑' p : Nat.Primes, ‖rowOp s p x‖ ^ 2 := hmain

end

end RHTower.PrimeCoShift
