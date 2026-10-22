import GaloisForLFunctions.RHTower.CCM.CCMLocalRatioArchimedean

/-!
# The completed local-ratio product and its quantized-differential kernel

The places of the completed local-ratio product are indexed by `Option ℕ`: `none` is the archimedean
place, `some p` the prime `p`.  Both kinds of multiplier have value one and purely imaginary first jet
at the seam, so the generic anomaly theorems apply to the completed family with no side conditions.

* `placeRatio`, `placeCharge`, `hasDerivAt_placeRatio` — the completed family and its first jets.
* `tendsto_completedCovarianceAnomaly_div_sq` — equations `(6)`–`(9)` for `V = {infinity} ∪ F`: the
  quadratic jet is `-((sum b)^(2 : ℕ) - sum b^(2 : ℕ))/2`.
* `completedCharge_pos` — it is **strictly** negative as soon as two places are present.
* `norm_placeRatio` — every local ratio is unimodular on the critical line.  The reason is structural:
  numerator and denominator are complex conjugates of each other, at the finite places because `r` is
  real, at the archimedean place because `Gamma` commutes with conjugation.
* `placePairKernel`, `quantizedDifferentialAnomaly`, `quantizedDifferentialAnomaly_diag`,
  `norm_kernelAnomaly_le` — section 4 of the card: the boundary kernel `(18)`, its vanishing on the
  diagonal, and the quantitative statement that the vanishing is of second order.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Finset Filter Topology

/-! ## The completed family -/

/-- The local ratio of a place: `none` is the archimedean place. -/
def placeRatio : Option ℕ → ℝ → ℂ
  | none => archRatio
  | some p => primeRatio p

/-- The first-jet magnitude of a place. -/
def placeCharge : Option ℕ → ℝ
  | none => archRatioCharge
  | some p => primeRatioCharge p

theorem placeRatio_zero (v : Option ℕ) : placeRatio v 0 = 1 := by
  cases v with
  | none => exact archRatio_zero
  | some p => exact primeRatio_zero p

theorem hasDerivAt_placeRatio (v : Option ℕ) :
    HasDerivAt (placeRatio v) (-Complex.I * ((placeCharge v : ℝ) : ℂ)) 0 := by
  cases v with
  | none => exact hasDerivAt_archRatio
  | some p => exact hasDerivAt_primeRatio p

theorem placeCharge_pos {v : Option ℕ} (h : ∀ p, v = some p → 2 ≤ p) : 0 < placeCharge v := by
  cases v with
  | none => exact archRatioCharge_pos
  | some p => exact primeRatioCharge_pos (h p rfl)

/-! ## The quadratic jet of the completed anomaly -/

/-- The quadratic jet of a covariance anomaly whose one-place jets are purely imaginary.  The sign
flip is the whole point: `(-i b)(-i b') = -b b'`, so the quadratic jet is negative. -/
theorem tendsto_covarianceAnomaly_div_sq_of_imaginary {ι : Type*} [DecidableEq ι]
    {u : ι → ℝ → ℂ} {b : ι → ℝ} (hu : ∀ v, u v 0 = 1)
    (hd : ∀ v, HasDerivAt (u v) (-Complex.I * ((b v : ℝ) : ℂ)) 0) (s : Finset ι) :
    Tendsto (fun t : ℝ => covarianceAnomaly s u t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((((∑ v ∈ s, b v) ^ (2 : ℕ) - ∑ v ∈ s, b v ^ (2 : ℕ)) / 2 : ℝ) : ℂ))) := by
  have h := tendsto_covarianceAnomaly_div_sq (u := u)
    (c := fun v => -Complex.I * ((b v : ℝ) : ℂ)) hu hd s
  have hsumcast : (∑ v ∈ s, -Complex.I * ((b v : ℝ) : ℂ))
      = -Complex.I * (((∑ v ∈ s, b v : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
  have hsq : ∀ v : ι, (-Complex.I * ((b v : ℝ) : ℂ)) ^ (2 : ℕ) = -(((b v ^ (2 : ℕ) : ℝ)) : ℂ) := by
    intro v
    push_cast
    have hI : (-Complex.I) ^ (2 : ℕ) = -1 := by
      rw [neg_pow, Complex.I_sq]
      norm_num
    rw [mul_pow, hI]
    ring
  have hval : (((∑ v ∈ s, -Complex.I * ((b v : ℝ) : ℂ)) ^ (2 : ℕ)
        - ∑ v ∈ s, (-Complex.I * ((b v : ℝ) : ℂ)) ^ (2 : ℕ)) / 2)
      = -((((∑ v ∈ s, b v) ^ (2 : ℕ) - ∑ v ∈ s, b v ^ (2 : ℕ)) / 2 : ℝ) : ℂ) := by
    rw [hsumcast, Finset.sum_congr rfl fun v _ => hsq v, Finset.sum_neg_distrib,
      ← Complex.ofReal_sum]
    push_cast
    have hI : (-Complex.I) ^ (2 : ℕ) = -1 := by
      rw [neg_pow, Complex.I_sq]
      norm_num
    rw [mul_pow, hI]
    ring
  rw [hval] at h
  exact h

/-- **Equations (6)–(9) for the completed product.** -/
theorem tendsto_completedCovarianceAnomaly_div_sq (V : Finset (Option ℕ)) :
    Tendsto (fun t : ℝ => covarianceAnomaly V placeRatio t / (t : ℂ) ^ (2 : ℕ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (-((((∑ v ∈ V, placeCharge v) ^ (2 : ℕ)
        - ∑ v ∈ V, placeCharge v ^ (2 : ℕ)) / 2 : ℝ) : ℂ))) :=
  tendsto_covarianceAnomaly_div_sq_of_imaginary placeRatio_zero hasDerivAt_placeRatio V

/-- **Strict negativity of the quadratic jet.**  As soon as two places are present the off-diagonal
charge is a nonempty sum of positive terms. -/
theorem completedCharge_pos {V : Finset (Option ℕ)}
    (hV : ∀ v ∈ V, 0 < placeCharge v) (hcard : 2 ≤ V.card) :
    0 < (∑ v ∈ V, placeCharge v) ^ (2 : ℕ) - ∑ v ∈ V, placeCharge v ^ (2 : ℕ) := by
  rw [offDiagCharge_eq_sum_offDiag]
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < V.card)
  refine Finset.sum_pos' (fun x hx => ?_) ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, ?_⟩
  · rw [Finset.mem_offDiag] at hx
    exact le_of_lt (mul_pos (hV x.1 hx.1) (hV x.2 hx.2.1))
  · exact mul_pos (hV a ha) (hV b hb)

/-! ## Unimodularity -/

theorem norm_div_conj {z : ℂ} (hz : z ≠ 0) : ‖z / (starRingEnd ℂ) z‖ = 1 := by
  rw [norm_div, RCLike.norm_conj]
  exact div_self (by simpa using hz)

theorem conj_primeLocalRatio_num (r L t : ℝ) :
    (starRingEnd ℂ) (1 - (r : ℂ) * Complex.exp (((L * t : ℝ) : ℂ) * Complex.I))
      = 1 - (r : ℂ) * Complex.exp (-(((L * t : ℝ) : ℂ) * Complex.I)) := by
  rw [map_sub, map_one, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- Every finite local ratio is unimodular on the critical line: numerator and denominator are
complex conjugates of each other. -/
theorem norm_primeLocalRatio {r : ℝ} (hr : |r| < 1) (L t : ℝ) :
    ‖primeLocalRatio r L t‖ = 1 := by
  rw [primeLocalRatio, ← conj_primeLocalRatio_num r L t]
  exact norm_div_conj (primeLocalRatio_num_ne_zero hr L t)

theorem gammaArch_conj (s : ℂ) :
    (starRingEnd ℂ) (gammaArch s) = gammaArch ((starRingEnd ℂ) s) := by
  have hlogpi : Complex.log (Real.pi : ℂ) = ((Real.log Real.pi : ℝ) : ℂ) :=
    (Complex.ofReal_log Real.pi_pos.le).symm
  have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  rw [gammaArch, gammaArch, map_mul, ← Complex.exp_conj, ← Complex.Gamma_conj, hlogpi,
    map_mul, map_neg, map_div₀, h2, Complex.conj_ofReal]

theorem gammaArch_line_ne_zero (t : ℝ) : gammaArch (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  rw [gammaArch]
  refine mul_ne_zero (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero ?_)
  intro m hm
  have hre : ((1 / 2 + (t : ℂ) * Complex.I) / 2).re = (-(m : ℂ)).re := by rw [hm]
  simp only [Complex.neg_re, Complex.natCast_re, Complex.div_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.mul_im] at hre
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  norm_num at hre
  linarith

/-- The archimedean local ratio is unimodular on the critical line, because `Gamma` commutes with
conjugation and `log pi` is real. -/
theorem norm_archRatio (t : ℝ) : ‖archRatio t‖ = 1 := by
  have hconj : gammaArch (1 / 2 - (t : ℂ) * Complex.I)
      = (starRingEnd ℂ) (gammaArch (1 / 2 + (t : ℂ) * Complex.I)) := by
    rw [gammaArch_conj]
    congr 1
    have h2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
    rw [map_add, map_mul, map_div₀, h2, map_one, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [archRatio, hconj]
  exact norm_div_conj (gammaArch_line_ne_zero t)

theorem norm_placeRatio (v : Option ℕ) (t : ℝ) : ‖placeRatio v t‖ = 1 := by
  cases v with
  | none => exact norm_archRatio t
  | some p => exact norm_primeLocalRatio (abs_primeRadius_lt_one p) _ t

/-! ## The quantized-differential kernel -/

/-- The boundary pair kernel of a place, `r_v(x, y) = conj(u_v(x)) u_v(y)`. -/
def placePairKernel (v : Option ℕ) (x y : ℝ) : ℂ :=
  (starRingEnd ℂ) (placeRatio v x) * placeRatio v y

/-- On the diagonal every pair kernel is one, because the local ratio is unimodular. -/
theorem placePairKernel_diag (v : Option ℕ) (x : ℝ) : placePairKernel v x x = 1 := by
  rw [placePairKernel, RCLike.conj_mul, norm_placeRatio v x]
  norm_num

/-- **Equation (18).**  The difference between the product of the pair kernels and the sum of the
one-place quantized differentials is the complete higher-than-linear part. -/
theorem quantizedDifferentialAnomaly (V : Finset (Option ℕ)) (x y : ℝ) :
    (∏ v ∈ V, placePairKernel v x y) - 1 - ∑ v ∈ V, (placePairKernel v x y - 1)
      = ∑ I ∈ V.powerset.filter fun I => 2 ≤ I.card,
          ∏ v ∈ I, (placePairKernel v x y - 1) := by
  have h := prod_one_add_sub_one_sub_sum V fun v => placePairKernel v x y - 1
  rw [← h]
  refine congrArg₂ _ (congrArg₂ _ ?_ rfl) rfl
  exact Finset.prod_congr rfl fun v _ => by ring

/-- The kernel anomaly vanishes on the diagonal. -/
theorem quantizedDifferentialAnomaly_diag (V : Finset (Option ℕ)) (x : ℝ) :
    (∏ v ∈ V, placePairKernel v x x) - 1 - ∑ v ∈ V, (placePairKernel v x x - 1) = 0 := by
  have hprod : (∏ v ∈ V, placePairKernel v x x) = 1 := by
    rw [Finset.prod_congr rfl fun v _ => placePairKernel_diag v x, Finset.prod_const_one]
  have hsum : (∑ v ∈ V, (placePairKernel v x x - 1)) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [placePairKernel_diag v x, sub_self]
  rw [hprod, hsum]
  ring

/-- **Quadratic diagonal vanishing.**  If every one-place increment is at most `D <= 1`, the anomaly is
at most `card · D²`: each surviving product has at least two factors.  With
`D = O(|y - x|)` this is the card's "at least quadratic diagonal vanishing", and it is what makes the
product against a first-order singular kernel vanish on the diagonal. -/
theorem norm_kernelAnomaly_le {ι : Type*} [DecidableEq ι] {V : Finset ι} {a : ι → ℂ} {D : ℝ}
    (hD0 : 0 ≤ D) (hD1 : D ≤ 1) (h : ∀ v ∈ V, ‖a v‖ ≤ D) :
    ‖∑ I ∈ V.powerset.filter fun I => 2 ≤ I.card, ∏ v ∈ I, a v‖
      ≤ ((V.powerset.filter fun I => 2 ≤ I.card).card : ℝ) * D ^ (2 : ℕ) := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ I ∈ V.powerset.filter fun I => 2 ≤ I.card, ‖∏ v ∈ I, a v‖ ≤ D ^ (2 : ℕ) := by
    intro I hI
    rw [Finset.mem_filter, Finset.mem_powerset] at hI
    have hprod : ‖∏ v ∈ I, a v‖ = ∏ v ∈ I, ‖a v‖ := norm_prod _ _
    have hle : (∏ v ∈ I, ‖a v‖) ≤ ∏ _v ∈ I, D :=
      Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v hv => h v (hI.1 hv))
    rw [Finset.prod_const] at hle
    have hcard : 2 ≤ I.card := hI.2
    have hpow : D ^ I.card ≤ D ^ (2 : ℕ) := pow_le_pow_of_le_one hD0 hD1 hcard
    rw [hprod]
    exact le_trans hle hpow
  simpa using Finset.sum_le_card_nsmul _ _ _ hterm

end GaloisForLFunctions.RHTower

end
